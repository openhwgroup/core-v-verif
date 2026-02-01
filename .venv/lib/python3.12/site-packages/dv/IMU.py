import dv.fb.IMU


class IMUSample(dv.fb.IMU.IMU):
    def __init__(self, fb_sample):
        self._fb_sample = fb_sample

    @property
    def timestamp(self):
        return self._fb_sample.Timestamp()

    @property
    def temperature(self):
        return self._fb_sample.Temperature()

    @property
    def accelerometer(self):
        return self._fb_sample.AccelerometerX(), self._fb_sample.AccelerometerY(), self._fb_sample.AccelerometerZ()

    @property
    def gyroscope(self):
        return self._fb_sample.GyroscopeX(), self._fb_sample.GyroscopeY(), self._fb_sample.GyroscopeZ()

    @property
    def magnetometer(self):
        return self._fb_sample.MagnetometerX(), self._fb_sample.MagnetometerY(), self._fb_sample.MagnetometerZ()

    @classmethod
    def from_fb(cls, obj):
        obj.__class__ = IMUSample
        return obj
