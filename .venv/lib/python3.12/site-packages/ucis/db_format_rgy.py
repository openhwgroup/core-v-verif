'''
Created on Jun 11, 2022

@author: mballance
'''
from ucis.xml.db_format_if_xml import DbFormatIfXml
from ucis.mem.db_format_if_mem import DbFormatIfMem
from ucis.yaml.db_format_if_yaml import DbFormatIfYaml
from ucis.lib.db_format_if_lib import DbFormatIfLib

class DbFormatRgy(object):
    
    _inst = None
    
    def __init__(self):
        self._fmt_if_m = {}
        self._fmt_desc_m = {}
        
    def addFormatIf(self, name, fmt_if, desc):
        self._fmt_if_m[name] = fmt_if
        
    def hasFormatType(self, name):
        return name in self._fmt_if_m.keys()
    
    def getFormats(self):
        return self._fmt_if_m.keys().copy()
    
    def getFormatIf(self, name):
        if name not in self._fmt_if_m.keys():
            raise Exception("Format %s not supported" % name)
        return self._fmt_if_m[name]()
        
    def init(self):
        self.addFormatIf("lib", DbFormatIfLib)
        self.addFormatIf("mem", DbFormatIfMem)
        self.addFormatIf("xml", DbFormatIfXml)
        self.addFormatIf("yml", DbFormatIfYaml)
        pass
    
    @classmethod
    def inst(cls):
        if cls._inst is None:
            cls._inst = cls()
            cls._inst.init()
        return cls._inst