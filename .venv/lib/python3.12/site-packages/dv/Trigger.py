import dv.fb.Trigger


class Trigger(dv.fb.Trigger.Trigger):
    def __init__(self, fb_trigger):
        self._fb_trigger = fb_trigger

    @property
    def timestamp(self):
        return self._fb_trigger.Timestamp()

    @property
    def type(self):
        return self._fb_trigger.Type()
