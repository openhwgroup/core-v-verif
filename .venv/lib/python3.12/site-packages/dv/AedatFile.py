import re
import sys
import dv.fb.IOHeader
import dv.fb.PacketHeader
import dv.fb.CompressionType
import dv.fb.EventPacket
import dv.fb.Frame
import dv.fb.IMUPacket
import dv.fb.TriggerPacket
import xml.etree.ElementTree as ET
import lz4.frame
import zstd

from dv import Event, Frame, Trigger, IMU


class _AedatFileIterator:
    def __init__(self, _aedat_file, stream_name):
        self._stream_name = stream_name
        self._aedat_file = _aedat_file
        self._stream_id = _aedat_file._name_id_map[stream_name]
        self._stream_info = _aedat_file._name_info_map[stream_name]
        self._file = open(_aedat_file._file_name, 'rb')
        self._file.seek(self._aedat_file._data_offset)
        self._packet = None
        self._packetIteratorPosition = -1

    def close(self):
        self._file.close()

    def __iter__(self):
        return self

    def __next__(self):
        if self._packet is None:
            self._read_next_packet()

    def __len__(self):
        raise NotImplementedError('Length of aedat streams is currently not implemented.')

    def source(self):
        if 'source' in self._stream_info:
            return self._stream_info['source']
        raise NameError('Source attribute not present for stream')

    def _read_next_packet(self):
        packet_header = dv.fb.PacketHeader.PacketHeader()

        while True:
            if self._aedat_file._data_table_position > 0 and self._file.tell() >= self._aedat_file._data_table_position:
                raise StopIteration

            packet_header_data = self._file.read(8)
            # we reached end of file, there is no next package
            if len(packet_header_data) < 8:
                raise StopIteration

            packet_header.Init(packet_header_data, 0)
            # use packet if part of our stream (same ID)
            if packet_header.StreamID() == self._stream_id:
                break

            self._file.seek(packet_header.Size(), 1)

        packet_data_compressed = self._file.read(packet_header.Size())
        packet_data = None
        if self._aedat_file._compression == dv.fb.CompressionType.CompressionType.NONE:
            packet_data = packet_data_compressed
        elif self._aedat_file._compression == dv.fb.CompressionType.CompressionType.LZ4 or self._aedat_file._compression == dv.fb.CompressionType.CompressionType.LZ4_HIGH:
            packet_data = lz4.frame.decompress(packet_data_compressed)
        elif self._aedat_file._compression == dv.fb.CompressionType.CompressionType.ZSTD or self._aedat_file._compression == dv.fb.CompressionType.CompressionType.ZSTD_HIGH:
            packet_data = zstd.decompress(packet_data_compressed)
        else:
            raise RuntimeError("File uses an unsupported type of data compression")

        self._packetIteratorPosition = 0
        self._parse_packet(packet_data)

    # gets overridden by child classes
    def _parse_packet(self, packet_data):
        pass


class _AedatFileEventIterator(_AedatFileIterator):
    def __init__(self, _aedat_file, stream_name):
        super().__init__(_aedat_file, stream_name)

    def _parse_packet(self, packet_data):
        self._packet = dv.fb.EventPacket.EventPacket.GetRootAsEventPacket(packet_data, 4)

    def __next__(self):
        super().__next__()
        event = Event(self._packet.Events(self._packetIteratorPosition))
        self._packetIteratorPosition += 1
        if self._packetIteratorPosition >= self._packet.EventsLength():
            self._packet = None
        return event

    @property
    def size_x(self):
        if 'sizeX' not in self._stream_info:
            raise KeyError('Size not present for stream')
        return int(self._stream_info['sizeX'])

    @property
    def size_y(self):
        if 'sizeY' not in self._stream_info:
            raise KeyError('Size not present for stream')
        return int(self._stream_info['sizeY'])

    @property
    def size(self):
        return self.size_y, self.size_x

    def numpy(self):
        return self._aedat_file.numpy_packet_iterator(self._stream_name)


class _AedatFileEventNumpyPacketIterator(_AedatFileIterator):
    def __init__(self, _aedat_file, stream_name):
        super().__init__(_aedat_file, stream_name)

    def _parse_packet(self, packet_data):
        self._packet = dv.fb.EventPacket.EventPacket.GetRootAsEventPacket(packet_data, 4)

    def __next__(self):
        super().__next__()
        buff = self._packet.EventsBufferAsNumpy()
        self._packet = None
        return buff


class _AedatFileFrameIterator(_AedatFileIterator):
    def __init__(self, _aedat_file, stream_name):
        super().__init__(_aedat_file, stream_name)

    def _parse_packet(self, packet_data):
        self._packet = dv.fb.Frame.Frame.GetRootAsFrame(packet_data, 4)

    def __next__(self):
        super().__next__()
        frame = Frame(self._packet)
        self._packet = None
        return frame

    @property
    def size_x(self):
        if 'sizeX' not in self._stream_info:
            raise KeyError('Size not present for stream')
        return int(self._stream_info['sizeX'])

    @property
    def size_y(self):
        if 'sizeY' not in self._stream_info:
            raise KeyError('Size not present for stream')
        return int(self._stream_info['sizeY'])

    @property
    def size(self):
        return self.size_y, self.size_x


class _AedatFileIMUIterator(_AedatFileIterator):
    def __init__(self, _aedat_file, stream_name):
        super().__init__(_aedat_file, stream_name)

    def _parse_packet(self, packet_data):
        self._packet = dv.fb.IMUPacket.IMUPacket.GetRootAsIMUPacket(packet_data, 4)

    def __next__(self):
        super().__next__()
        sample = IMU.IMUSample(self._packet.Samples(self._packetIteratorPosition))
        self._packetIteratorPosition += 1
        if self._packetIteratorPosition >= self._packet.SamplesLength():
            self._packet = None
        return sample


class _AedatFileTriggerIterator(_AedatFileIterator):
    def __init__(self, _aedat_file, stream_name):
        super().__init__(_aedat_file, stream_name)

    def _parse_packet(self, packet_data):
        self._packet = dv.fb.TriggerPacket.TriggerPacket.GetRootAsTriggerPacket(packet_data, 4)

    def __next__(self):
        super().__next__()
        trigger = Trigger(self._packet.Triggers(self._packetIteratorPosition))
        self._packetIteratorPosition += 1
        if self._packetIteratorPosition >= self._packet.TriggersLength():
            self._packet = None
        return trigger


class AedatFile:
    def __init__(self, file_name):
        self._file_name = file_name
        self._file = open(file_name, 'rb')
        self._parse_version_string(self._file.readline())
        self._name_id_map = {}
        self._name_type_map = {}
        self._name_info_map = {}
        self._parse_io_header()
        self._data_offset = self._file.tell()
        self._file.close()
        self._name_iterator_map = {}

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        self.close()

    def __del__(self):
        self.close()

    def close(self):
        self._file.close()
        for name, iterator in self._name_iterator_map.items():
            iterator.close()

    def _parse_version_string(self, version_string):
        v4 = re.compile('.*#!AER-DAT4.*')
        if v4.match(str(version_string)):
            self.version = 4
        else:
            print("Unrecognized or unsupported version: %s" % str(version_string).strip(), file=sys.stderr)

    def _parse_io_header(self):
        header_length = int.from_bytes(self._file.read(4), byteorder='little')
        header_data = self._file.read(header_length)
        header = dv.fb.IOHeader.IOHeader.GetRootAsIOHeader(header_data, 0)
        self._compression = header.Compression()
        self._data_table_position = header.DataTablePosition()
        self._info_node_string = header.InfoNode()

        # parse xml
        name_clash_counter = {}
        xml_root = ET.fromstring(self._info_node_string)
        for output_node in xml_root[0]:
            # get all children attr tags
            child_attrs = {child.attrib['key']: child.text for child in output_node if child.tag == 'attr'}
            name = child_attrs['originalOutputName']
            if name in name_clash_counter:
                name_clash_counter[name] += 1
            else:
                name_clash_counter[name] = 0
            clash_free_name = name if name_clash_counter[name] == 0 else ('%s_%d' % (name, name_clash_counter[name]))
            self._name_id_map[clash_free_name] = int(output_node.attrib['name'])
            self._name_type_map[clash_free_name] = child_attrs['typeIdentifier']

            for c in output_node:
                if c.tag == 'node' and c.attrib['name'] == 'info':
                    self._name_info_map[clash_free_name] = {a.attrib['key']: a.text for a in c if a.tag == 'attr'}
                    break

    @property
    def names(self):
        return list(self._name_id_map.keys())

    def __getitem__(self, name):
        if name not in self._name_id_map:
            raise RuntimeError('Stream named %s not in file. Available are %s' % (name, str(self.names)))

        # iterator already present
        if name in self._name_iterator_map:
            return self._name_iterator_map[name]

        iterator = None
        if self._name_type_map[name] == 'EVTS':
            iterator = _AedatFileEventIterator(self, name)
        elif self._name_type_map[name] == 'FRME':
            iterator = _AedatFileFrameIterator(self, name)
        elif self._name_type_map[name] == 'IMUS':
            iterator = _AedatFileIMUIterator(self, name)
        elif self._name_type_map[name] == 'TRIG':
            iterator = _AedatFileTriggerIterator(self, name)
        else:
            raise RuntimeError('Unknown datatype %s for stream with name %s' % (self._name_type_map[name], name))

        self._name_iterator_map[name] = iterator
        return iterator

    def numpy_packet_iterator(self, name):
        if name not in self._name_id_map:
            raise RuntimeError('Stream named %s not in file. Available are %s' % (name, str(self.names)))
        if self._name_type_map[name] != 'EVTS':
            raise RuntimeError('Numpy packet iterators are only supported for streams of event type')
        if name + '_np' in self._name_iterator_map:
            return self._name_iterator_map[name + '_np']
        iterator = _AedatFileEventNumpyPacketIterator(self, name)
        self._name_iterator_map[name + '_np'] = iterator
        return iterator
