'''
Created on Jun 11, 2022

@author: mballance
'''
from ucis.rgy.format_if_db import FormatIfDb, FormatDescDb, FormatDbFlags
from .xml_ucis import XmlUCIS

class DbFormatIfXml(FormatIfDb):
    
    def init(self, options):
        raise Exception("Options %s not accepted by the XML format" % str(options))
    
    def create(self, filename=None):
        return XmlUCIS()
    
    def read(self, file_or_filename) -> 'UCIS':
        from ucis.xml.xml_factory import XmlFactory
        return XmlFactory.read(file_or_filename)
    
    @staticmethod        
    def register(rgy):
        rgy.addDatabaseFormat(FormatDescDb(
            DbFormatIfXml,
            name="xml",
            description="Supports reading and writing UCIS XML interchange",
            flags=FormatDbFlags.Read|FormatDbFlags.Write))
        
        