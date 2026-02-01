import numpy as np


class EventFrameIterator:
    def __init__(self, file, frameTime, shape):
        self.file = file
        self.frameTime = frameTime
        self.shape = shape
        self._iterator = iter(file)

    def __iter__(self):
        return self

    def __next__(self):
        frame = np.zeros(self.shape)
        first_event_time = -1
        for event in self._iterator:
            if first_event_time < 0:
                first_event_time = event.timestamp
            frame[self.shape[0] - event.y - 1, event.x] += 1 if event.polarity else -1
            if event.timestamp - first_event_time >= self.frameTime * 1000:
                break

        if first_event_time < 0:
            raise StopIteration
        return frame
