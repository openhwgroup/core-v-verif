import numpy as np

from dv.fb.FrameFormat import FrameFormat


class Frame:
    def __init__(self, fb_frame):
        self._fb_frame = fb_frame

    @property
    def timestamp(self):
        return self._fb_frame.Timestamp()

    @property
    def timestamp_start_of_frame(self):
        return self._fb_frame.TimestampStartOfFrame()

    @property
    def timestamp_end_of_frame(self):
        return self._fb_frame.TimestampEndOfFrame()

    @property
    def timestamp_start_of_exposure(self):
        return self._fb_frame.TimestampStartOfExposure()

    @property
    def timestamp_end_of_exposure(self):
        return self._fb_frame.TimestampEndOfExposure()

    @property
    def size(self):
        return self._fb_frame.SizeX(), self._fb_frame.SizeY()

    @property
    def position(self):
        return self._fb_frame.PositionX(), self._fb_frame.PositionY()

    @property
    def image(self):
        channels = 1
        pixel_format = self._fb_frame.Format()
        if pixel_format == FrameFormat.BGR:
            channels = 3
        elif pixel_format == FrameFormat.BGRA:
            channels = 4
        return np.reshape(self._fb_frame.PixelsAsNumpy(), (self.size[1], self.size[0], channels))
