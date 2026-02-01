import dv.fb.Event


class Event(dv.fb.Event.Event):
    def __init__(self, fb_event):
        self._fb_event = fb_event

    @property
    def x(self):
        return self._fb_event.X()

    @property
    def y(self):
        return self._fb_event.Y()

    @property
    def polarity(self):
        return self._fb_event.Polarity()

    @property
    def timestamp(self):
        return self._fb_event.Timestamp()

    def __str__(self):
        return '{} ({:3d} {:3d}) | {:8d}'.format('+' if self._fb_event.Polarity() else '-', self._fb_event.X(),
                                                 self._fb_event.Y(), self._fb_event.Timestamp())

    @classmethod
    def from_fb(cls, obj):
        obj.__class__ = Event
        return obj
