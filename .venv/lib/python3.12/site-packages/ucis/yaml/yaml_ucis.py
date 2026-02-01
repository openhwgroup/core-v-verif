
from ucis.mem import MemUCIS

class YamlUCIS(MemUCIS):

    def write(self, file, scope=None, recurse=True, covertype=-1):
        raise Exception("YamlUCIS.write not implemented")