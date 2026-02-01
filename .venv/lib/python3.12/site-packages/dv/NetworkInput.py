import socket

import dv.fb.Frame
import dv.fb.Event
import dv.fb.IMU
import dv.fb.Trigger

import dv.fb.EventPacket
import dv.fb.FrameFormat
import dv.fb.IMUPacket
import dv.fb.TriggerPacket

from dv import Frame, Trigger, Event, IMU


class _NetworkInput:
    def __init__(self, address, port):
        self._address = address
        self._port = port
        self._socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self._socket.connect((address, port))
        self._packet = None
        self._packetIteratorPosition = -1

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        self._socket.close()

    def __del__(self):
        self._socket.close()

    def __iter__(self):
        return self

    def __next__(self):
        if self._packet is None:
            self._receive_next_packet()

    def _receive_next_packet(self):
        io_header = self._socket.recv(8, socket.MSG_WAITALL)
        length = int.from_bytes(io_header[4:], byteorder='little')
        packet_data = self._socket.recv(length, socket.MSG_WAITALL)
        packet_data = packet_data[4:]
        self._packetIteratorPosition = 0
        self._parse_packet(packet_data)

    def _parse_packet(self, packet_data):
        pass


class NetworkEventInput(_NetworkInput):
    def __init__(self, address='127.0.0.1', port=7777):
        super().__init__(address, port)

    def _parse_packet(self, packet_data):
        self._packet = dv.fb.EventPacket.EventPacket.GetRootAsEventPacket(packet_data, 0)

    def __next__(self):
        super().__next__()
        event = Event.Event(self._packet.Events(self._packetIteratorPosition))
        self._packetIteratorPosition += 1
        if self._packetIteratorPosition >= self._packet.EventsLength():
            self._packet = None
        return event


class NetworkNumpyEventPacketInput(_NetworkInput):
    def __init__(self, address='127.0.0.1', port=7777):
        super().__init__(address, port)

    def _parse_packet(self, packet_data):
        self._packet = dv.fb.EventPacket.EventPacket.GetRootAsEventPacket(packet_data, 0)

    def __next__(self):
        super().__next__()
        buff = self._packet.EventsBufferAsNumpy()
        self._packet = None
        return buff


class NetworkFrameInput(_NetworkInput):
    def __init__(self, address='127.0.0.1', port=7777):
        super().__init__(address, port)

    def _parse_packet(self, packet_data):
        self._packet = dv.fb.Frame.Frame.GetRootAsFrame(packet_data, 0)

    def __next__(self):
        super().__next__()
        frame = Frame.Frame(self._packet)
        self._packet = None
        return frame


class NetworkIMUInput(_NetworkInput):
    def __init__(self, address='127.0.0.1', port=7777):
        super().__init__(address, port)

    def _parse_packet(self, packet_data):
        self._packet = dv.fb.IMUPacket.IMUPacket.GetRootAsIMUPacket(packet_data, 0)

    def __next__(self):
        super().__next__()
        sample = IMU.IMUSample(self._packet.Samples(self._packetIteratorPosition))
        self._packetIteratorPosition += 1
        if self._packetIteratorPosition >= self._packet.SamplesLength():
            self._packet = None
        return sample


class NetworkTriggerInput(_NetworkInput):
    def __init__(self, address='127.0.0.1', port=7777):
        super().__init__(address, port)

    def _parse_packet(self, packet_data):
        self._packet = dv.fb.TriggerPacket.TriggerPacket.GetRootAsTriggerPacket(packet_data, 0)

    def __next__(self):
        super().__next__()
        trigger = Trigger.Trigger(self._packet.Triggers(self._packetIteratorPosition))
        self._packetIteratorPosition += 1
        if self._packetIteratorPosition >= self._packet.TriggersLength():
            self._packet = None
        return trigger
