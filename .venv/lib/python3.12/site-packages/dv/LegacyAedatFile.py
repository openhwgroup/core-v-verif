import struct
import re
import sys
import numpy as np
from enum import Enum


class Type(Enum):
    Event = 0
    Frame = 1


class LegacyEvent:
    def __init__(self, x, y, polarity, timestamp):
        self.x = x
        self.y = y
        self.polarity = polarity
        self.timestamp = timestamp
        self.type = Type.Event

    def __str__(self):
        return '{} ({:3d} {:3d}) | {:8d}'.format('+' if self.polarity else '-', self.x, self.y, self.timestamp)


class LegacyFrame:
    def __init__(self, width, height):
        self.image = np.zeros((height, width), dtype='uint8')
        self.start_of_frame = -1
        self.end_of_frame = -1
        self.start_of_exposure = -1
        self.end_of_exposure = -1
        self.reset_count = 0
        self.signal_count = 0
        self.type = Type.Frame


class LegacyAedatFile:
    def __init__(self, fileName, frame_width=346, frame_height=260, enable_frames=False):
        self.enable_frames = enable_frames
        self.frame_height = frame_height
        self.frame_width = frame_width
        self.file = open(fileName, 'rb')
        self.version = self._parse_version_string(self.file.readline())
        self.file.seek(0, 0)  # rewind
        self._skip_ascii_header()
        self._generator = self._get_event_generator()

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        self.file.close()

    def __del__(self):
        self.file.close()

    def _parse_version_string(self, version_string):
        v2 = re.compile('.*AER-DAT2\.0.*')
        v3 = re.compile('.*#!AER-DAT3.*')
        if v2.match(str(version_string)):
            return 2
        elif v3.match(str(version_string)):
            return 3
        else:
            print("Unrecognized or unsupported version: %s" % str(version_string).strip(), file=sys.stderr)

    def _skip_ascii_header(self):
        if self.version == 2:
            self._skip_ascii_header_v2()
        elif self.version == 3:
            self._skip_ascii_header_v3()

    def _skip_ascii_header_v2(self):
        last_pos = 0
        line = self.file.readline()
        while line.startswith(b'#'):
            last_pos = self.file.tell()
            line = self.file.readline(10000)
        self.file.seek(last_pos, 0)

    def _skip_ascii_header_v3(self):
        ''' skip ascii header '''
        line = self.file.readline()
        while line.startswith(b'#'):
            if line == b'#!END-HEADER\r\n':
                break
            else:
                line = self.file.readline()

    def _get_event_generator(self):
        if self.version == 2:
            return self._read_event_v2()
        elif self.version == 3:
            return self._read_event_v3()
        else:
            print("Unsupported version", file=sys.stderr)

    def __iter__(self):
        return self

    def __next__(self):
        return next(self._generator)

    def _read_event_v2(self):
        """Returns generator to read individual events from v3 type files"""
        tsoverflow = 0
        last_timestamp32 = -1
        current_frame = LegacyFrame(self.frame_width, self.frame_height)
        while True:
            data = self.file.read(8)

            if not data:
                break

            address = struct.unpack('>I', data[0:4])[0]
            timestamp32 = struct.unpack('>I', data[4:8])[0]

            y = (address & 0x7FC00000) >> 22
            x = (address & 0x3FF000) >> 12
            if timestamp32 < last_timestamp32:
                tsoverflow += 1

            last_timestamp32 = timestamp32
            timestamp = timestamp32 | tsoverflow << 31

            if (address >> 31) & 0x1 > 0:  # non polarity data
                if not self.enable_frames:
                    continue

                type_info = (address & 0xC00) >> 10
                adc_value = (address & 0x3FF) >> 2
                if type_info == 0:  # aps reset read
                    if current_frame.reset_count == 0:
                        current_frame.start_of_frame = timestamp
                    current_frame.start_of_exposure = timestamp
                    current_frame.image[self.frame_height - y - 1, x] = adc_value
                    current_frame.reset_count += 1
                elif type_info == 1:  # aps signal read
                    if current_frame.signal_count == 0:
                        current_frame.end_of_exposure = timestamp
                    current_frame.end_of_frame = timestamp

                    resetValue = current_frame.image[self.frame_height - y - 1, x]
                    signalValue = adc_value
                    pixelValue = 0

                    # 256 to better work with unchanged DAVIS240 values
                    if (resetValue < 256) or (signalValue == 0):
                        pixelValue = 1023
                    else:
                        pixelValue = resetValue - signalValue
                        pixelValue = max(pixelValue, 0)
                        pixelValue = min(pixelValue, 1023)

                    current_frame.image[self.frame_height - y - 1, x] = (pixelValue >> 2)
                    current_frame.signal_count += 1

                if current_frame.signal_count >= self.frame_height * self.frame_width:
                    yield current_frame
                    current_frame = LegacyFrame(self.frame_width, self.frame_height)

            else:  #polarity data
                pol_info = (address & 0xC00) >> 10
                polarity = pol_info == 2
                yield LegacyEvent(x, y, polarity, timestamp)

    def _read_event_v3(self):
        """Returns generator to read individual events from v3 type files"""
        while True:
            header = self.file.read(28)
            if not header or len(header) == 0:
                break

            # read header
            type = struct.unpack('H', header[0:2])[0]
            source = struct.unpack('H', header[2:4])[0]
            size = struct.unpack('I', header[4:8])[0]
            offset = struct.unpack('I', header[8:12])[0]
            tsoverflow = struct.unpack('I', header[12:16])[0]
            capacity = struct.unpack('I', header[16:20])[0]
            number = struct.unpack('I', header[20:24])[0]
            valid = struct.unpack('I', header[24:28])[0]

            data_length = capacity * size
            data = self.file.read(data_length)
            counter = 0

            if type == 1:
                while data[counter:counter + size]:
                    aer_data = struct.unpack('I', data[counter:counter + 4])[0]
                    timestamp = struct.unpack('I', data[counter + 4:counter + 8])[0] | tsoverflow << 31
                    x = (aer_data >> 17) & 0x00007FFF
                    y = (aer_data >> 2) & 0x00007FFF
                    pol = (aer_data >> 1) & 0x00000001
                    counter = counter + size
                    yield LegacyEvent(x, y, pol, timestamp)
            else:
                # non-polarity event packet, not implemented
                pass
