
from ucis.mem import MemUCIS
from .xml_writer import XmlWriter

class XmlUCIS(MemUCIS):

    def write(self, file, scope=None, recurse=True, covertype=-1):

        writer = XmlWriter()

        with open(file, "w") as fp:
            writer.write(fp, self)
