/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * sensors.ssc_fusedlight: a thin, open-source wrapper around the stock
 * Qualcomm sensors.ssc.so sub-HAL for Redmi Note 10 Pro (sweet).
 *
 * The stock HAL exposes two light sensors:
 *   - android.sensor.light      (type 5)        front ALS (TSL2540 or BU27030)
 *   - xiaomi.sensor.back_lux    (type 33171055) rear ALS next to the cameras
 *
 * AOSP's auto-brightness only listens to type 5. This wrapper keeps every
 * sensor as-is, but whenever something enables the front light sensor it
 * also enables the rear one internally and rewrites the front sensor's lux
 * with a fused value. The framework needs no changes.
 *
 * Loaded by the legacy multi-HAL through /vendor/etc/sensors/hals.conf,
 * in place of sensors.ssc.so.
 */

#define LOG_TAG "FusedLight"

#include <dlfcn.h>
#include <fcntl.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>
#include <string.h>

#include <algorithm>
#include <cmath>
#include <mutex>
#include <vector>

#include <cutils/properties.h>
#include <hardware/hardware.h>
#include <hardware/sensors.h>
#include <log/log.h>

namespace {

constexpr const char* kInnerLib = "sensors.ssc.so";
constexpr int32_t kTypeBackLux = 33171055;  // xiaomi.sensor.back_lux

// ---- Policy, ported from stock MIUI (miui-services.jar) ---------------------
// DualSensorPolicy / AutomaticBrightnessControllerImpl on stock sweet:
//  - Front ("main") sensor drives brightness by default.
//  - Switch to the rear ("assist") sensor when it reads above the front
//    sensor's brightening threshold, or when the front darkens past its
//    darkening threshold while the rear is still brighter.
//  - Stay on the rear while it reads brighter than the front; go back to
//    the front as soon as front >= rear.
//  - Ignore the rear while the torch/flash is on and for 1800 ms after.
// The framework's own ring buffer + debounce smooths whatever we report,
// exactly like MIUI does for each sensor.
//
// Hysteresis tables: stock FrameworksResTarget.apk (values in 1/1000).
// Ship the same arrays in the overlay so the framework uses them too.
constexpr float kThresholdLevels[] = {2, 10, 30, 100, 800, 2000, 4000};
constexpr float kBrighten[] = {2, 5, 10, 30, 100, 400, 600, 1000};
constexpr float kDarken[] = {800, 800, 500, 500, 500, 500, 500, 500};
constexpr int64_t kTorchHoldoffNs = 1800LL * 1000000LL;  // TORCH_CLOSE_DELAY
// Re-send a synthetic front event when a rear change moves the output >2%.
constexpr float kMinDelta = 0.02f;
constexpr const char* kFlashSwitch = "/sys/class/leds/led:switch_0/brightness";

int levelIndex(float lux) {
    int i = 0;
    while (i < (int)(sizeof(kThresholdLevels) / sizeof(kThresholdLevels[0])) &&
           lux >= kThresholdLevels[i])
        i++;
    return i;
}
float brightenThr(float lux) { return lux * (1.f + kBrighten[levelIndex(lux)] / 1000.f); }
float darkenThr(float lux) { return lux * (1.f - kDarken[levelIndex(lux)] / 1000.f); }

sensors_module_t* gInnerModule = nullptr;

struct State {
    std::mutex lock;
    sensors_poll_device_1_t* inner = nullptr;
    int frontHandle = -1;
    int backHandle = -1;
    bool frontOn = false;    // framework asked for front
    bool backClient = false; // framework asked for rear itself
    bool backHwOn = false;   // what we last told the inner HAL
    int64_t frontPeriodNs = 200000000;
    float frontLux = -1.f;
    float rearLux = -1.f;
    float lastFused = -1.f;
    float frontRef = -1.f;   // front lux the current thresholds are based on
    bool useRear = false;    // MIUI USE_ASSIST_LIGHT_SENSOR
    int64_t torchOffNs = 0;  // when the flash last turned off
    bool torchOn = false;
    bool enabled = true;     // persist.sensor.fusedlight (default on)
};
State gState;

int64_t nowNs() {
    timespec ts;
    clock_gettime(CLOCK_BOOTTIME, &ts);
    return ts.tv_sec * 1000000000LL + ts.tv_nsec;
}

// MIUI checkAssistSensorValid(): no rear data while the flash is on or
// within 1800 ms of it turning off (the flash sits right next to the sensor).
bool rearValid() {
    int fd = open(kFlashSwitch, O_RDONLY | O_CLOEXEC);
    bool on = false;
    if (fd >= 0) {
        char buf[8] = {};
        if (read(fd, buf, sizeof(buf) - 1) > 0) on = atoi(buf) > 0;
        close(fd);
    }
    int64_t now = nowNs();
    if (gState.torchOn && !on) gState.torchOffNs = now;
    gState.torchOn = on;
    return !on && now - gState.torchOffNs > kTorchHoldoffNs;
}

// Port of DualSensorPolicy.updateDualSensorPolicy(). Called with lock held.
float fuse(float front, float rear) {
    if (front < 0.f) return rear < 0.f ? 0.f : rear;
    if (!gState.enabled || rear < 0.f) {
        gState.useRear = false;
        gState.frontRef = front;
        return front;
    }
    if (gState.frontRef < 0.f) gState.frontRef = front;
    if (gState.useRear) {
        if (front >= rear) {
            gState.useRear = false;  // "switch main light sensor ... from assist"
            gState.frontRef = front;
        }
    } else {
        bool rearAboveMain = rear > brightenThr(gState.frontRef);
        bool mainDarkened = front <= darkenThr(gState.frontRef) && rear > front;
        if (rearAboveMain || mainDarkened) {
            gState.useRear = true;   // "update ambient lux using assist"
        } else if (front > brightenThr(gState.frontRef) ||
                   front < darkenThr(gState.frontRef)) {
            gState.frontRef = front; // main crossed its own threshold
        }
    }
    return gState.useRear ? rear : front;
}

bool movedEnough(float a, float b) {
    if (b < 0.f) return true;
    float base = std::max(b, 1.f);
    return std::abs(a - b) / base > kMinDelta;
}

// Rear must run in hardware if a client wants it OR the front is on.
// Called with gState.lock held.
void syncBack() {
    auto* in = gState.inner;
    if (gState.backHandle < 0) return;
    bool want = gState.backClient || gState.frontOn;
    if (want == gState.backHwOn) return;
    if (want && !gState.backClient) {
        in->batch(in, gState.backHandle, 0, gState.frontPeriodNs, 0);
    }
    in->activate(&in->v0, gState.backHandle, want);
    gState.backHwOn = want;
    gState.rearLux = -1.f;
}

int wActivate(sensors_poll_device_t* /*dev*/, int handle, int enabled) {
    auto* in = gState.inner;
    std::lock_guard<std::mutex> l(gState.lock);
    if (handle >= 0 && handle == gState.backHandle) {
        gState.backClient = enabled;
        syncBack();
        return 0;
    }
    int ret = in->activate(&in->v0, handle, enabled);
    if (handle == gState.frontHandle && ret == 0) {
        gState.frontOn = enabled;
        if (enabled) {
            gState.frontLux = -1.f;
            gState.lastFused = -1.f;
            gState.frontRef = -1.f;
            gState.useRear = false;
            gState.enabled = property_get_bool("persist.sensor.fusedlight", true);
        }
        syncBack();
    }
    return ret;
}

int wSetDelay(sensors_poll_device_t* dev, int handle, int64_t ns) {
    (void)dev;
    auto* in = gState.inner;
    return in->v0.setDelay(&in->v0, handle, ns);
}

int wBatch(sensors_poll_device_1_t* dev, int handle, int flags, int64_t period, int64_t timeout) {
    (void)dev;
    auto* in = gState.inner;
    std::lock_guard<std::mutex> l(gState.lock);
    if (handle == gState.frontHandle) {
        gState.frontPeriodNs = period;
        if (gState.backHwOn && !gState.backClient) {
            in->batch(in, gState.backHandle, 0, period, 0);
        }
    }
    return in->batch(in, handle, flags, period, timeout);
}

int wFlush(sensors_poll_device_1_t* dev, int handle) {
    (void)dev;
    auto* in = gState.inner;
    return in->flush(in, handle);
}

// Rewrites/compacts events in place. Returns the new count.
int filterEvents(sensors_event_t* data, int n) {
    std::lock_guard<std::mutex> l(gState.lock);
    int out = 0;
    for (int i = 0; i < n; i++) {
        sensors_event_t& e = data[i];
        bool isBack = gState.backHandle >= 0 && e.sensor == gState.backHandle;
        if (isBack && e.type == SENSOR_TYPE_META_DATA) {
            if (gState.backClient) data[out++] = e;
            continue;
        }
        if (isBack) {
            // Drop rear samples around flash use, like MIUI does.
            gState.rearLux = rearValid() ? e.data[0] : -1.f;
            if (gState.backClient) {
                // A real client wants the rear sensor: pass it through. The
                // fused front value catches up on the next front event.
                data[out++] = e;
            } else if (gState.frontOn && gState.frontLux >= 0.f) {
                // Rear changed while front is stable: reuse this slot for a
                // synthetic front event (out <= i, so this never overwrites
                // an unread event).
                float f = fuse(gState.frontLux, gState.rearLux);
                if (movedEnough(f, gState.lastFused)) {
                    sensors_event_t s = e;
                    s.sensor = gState.frontHandle;
                    s.type = SENSOR_TYPE_LIGHT;
                    memset(s.data, 0, sizeof(s.data));
                    s.light = f;
                    gState.lastFused = f;
                    data[out++] = s;
                }
            }
            continue;
        }
        if (e.type == SENSOR_TYPE_LIGHT && e.sensor == gState.frontHandle) {
            gState.frontLux = e.light;
            float f = fuse(gState.frontLux, gState.rearLux);
            ALOGV("front=%.1f rear=%.1f fused=%.1f", gState.frontLux, gState.rearLux, f);
            e.light = f;
            gState.lastFused = f;
        }
        data[out++] = e;
    }
    return out;
}

int wPoll(sensors_poll_device_t* /*dev*/, sensors_event_t* data, int count) {
    auto* in = gState.inner;
    for (;;) {
        int n = in->v0.poll(&in->v0, data, count);
        if (n <= 0) return n;
        int out = filterEvents(data, n);
        // Only internal rear events arrived: block again rather than return 0.
        if (out > 0) return out;
    }
}

int wInject(sensors_poll_device_1_t* dev, const sensors_event_t* ev) {
    (void)dev;
    auto* in = gState.inner;
    return in->inject_sensor_data ? in->inject_sensor_data(in, ev) : -EINVAL;
}

int wRegisterDirect(sensors_poll_device_1_t* dev, const sensors_direct_mem_t* mem, int ch) {
    (void)dev;
    auto* in = gState.inner;
    return in->register_direct_channel ? in->register_direct_channel(in, mem, ch) : -EINVAL;
}

int wConfigDirect(sensors_poll_device_1_t* dev, int handle, int ch,
                  const struct sensors_direct_cfg_t* cfg) {
    (void)dev;
    auto* in = gState.inner;
    return in->config_direct_report ? in->config_direct_report(in, handle, ch, cfg) : -EINVAL;
}

int wClose(hw_device_t* dev) {
    auto* in = gState.inner;
    int ret = in->common.close(&in->common);
    delete reinterpret_cast<sensors_poll_device_1_t*>(dev);
    gState.inner = nullptr;
    return ret;
}

bool loadInner() {
    if (gInnerModule) return true;
    void* h = dlopen(kInnerLib, RTLD_LAZY);  // same flags the multi-HAL uses
    if (!h) {
        ALOGE("dlopen %s failed: %s", kInnerLib, dlerror());
        return false;
    }
    gInnerModule = static_cast<sensors_module_t*>(dlsym(h, HAL_MODULE_INFO_SYM_AS_STR));
    if (!gInnerModule) {
        ALOGE("%s has no HMI", kInnerLib);
        return false;
    }
    return true;
}

int wGetSensorsList(sensors_module_t* /*m*/, sensor_t const** list) {
    if (!loadInner()) return 0;
    int n = gInnerModule->get_sensors_list(gInnerModule, list);
    for (int i = 0; i < n; i++) {
        const sensor_t& s = (*list)[i];
        bool wake = s.flags & SENSOR_FLAG_WAKE_UP;
        if (wake) continue;  // fuse only the non-wakeup pair
        if (s.type == SENSOR_TYPE_LIGHT && gState.frontHandle < 0) gState.frontHandle = s.handle;
        if (s.type == kTypeBackLux && gState.backHandle < 0) gState.backHandle = s.handle;
    }
    ALOGI("front light handle=%d, rear (back_lux) handle=%d", gState.frontHandle,
          gState.backHandle);
    return n;
}

int wOpen(const hw_module_t* /*module*/, const char* id, hw_device_t** device) {
    if (!loadInner()) return -ENODEV;
    // Do NOT call get_sensors_list() here. sensors.ssc.so initializes on its
    // first get_sensors_list(); doing that from open(), on the service's main
    // thread before the device is open, makes every SSC attribute request
    // time out ("retrieve_attributes ... pending = 28") and the HAL reports
    // zero sensors. Keep the stock order: open first, list later (the
    // multi-HAL asks for the list itself, which fills in our handles).
    hw_device_t* innerDev = nullptr;
    int ret = gInnerModule->common.methods->open(&gInnerModule->common, id, &innerDev);
    if (ret) return ret;
    gState.inner = reinterpret_cast<sensors_poll_device_1_t*>(innerDev);

    auto* d = new sensors_poll_device_1_t(*gState.inner);  // copies version/tag
    d->common.close = wClose;
    d->activate = wActivate;
    d->setDelay = wSetDelay;
    d->poll = wPoll;
    d->batch = wBatch;
    d->flush = wFlush;
    d->inject_sensor_data = wInject;
    d->register_direct_channel = wRegisterDirect;
    d->config_direct_report = wConfigDirect;
    *device = &d->common;
    return 0;
}

int wSetOperationMode(unsigned int mode) {
    if (!loadInner()) return -EINVAL;
    return gInnerModule->set_operation_mode ? gInnerModule->set_operation_mode(mode) : -EINVAL;
}

hw_module_methods_t gMethods = {.open = wOpen};

}  // namespace

extern "C" {
__attribute__((visibility("default"))) sensors_module_t HAL_MODULE_INFO_SYM = {
        .common =
                {
                        .tag = HARDWARE_MODULE_TAG,
                        .module_api_version = SENSORS_MODULE_API_VERSION_0_1,
                        .hal_api_version = HARDWARE_HAL_API_VERSION,
                        .id = SENSORS_HARDWARE_MODULE_ID,
                        .name = "sweet fused light wrapper for sensors.ssc",
                        .author = "OSS",
                        .methods = &gMethods,
                },
        .get_sensors_list = wGetSensorsList,
        .set_operation_mode = wSetOperationMode,
};
}
