'''
Created on Jun 11, 2022

@author: mballance
'''
from ucis.db_format_if import DbFormatIf
from ucis.ucis import UCIS
from ucis.mem.mem_ucis import MemUCIS


class DbFormatIfMem(DbFormatIf):
    
    def init(self, options):
        raise Exception("Options %s not accepted by the Mem format" % str(options))
    
    def create(self) -> UCIS:
        return MemUCIS()
    
    def read(self, file_or_filename) -> UCIS:
        raise Exception("The Mem format can only be created, not read and written")
    
    def write(self, db : UCIS, file_or_filename):
        raise Exception("The Mem format can only be created, not read and written")