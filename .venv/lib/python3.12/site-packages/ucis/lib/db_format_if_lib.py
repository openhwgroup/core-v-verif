'''
Created on Jun 11, 2022

@author: mballance
'''
from ucis.rgy.format_if_db import FormatIfDb, FormatDescDb, FormatDbFlags


class DbFormatIfLib(FormatIfDb):
    
    def __init__(self):
        super().__init__()
        self.lib = None
    
    def init(self, options):
        raise NotImplementedError("DbFormatIf.init not implemented by %s" % str(type(self)))
    
    def create(self) -> 'UCIS':
        from ucis.lib.lib_ucis import LibUCIS
        lib = self._get_lib()
        if lib is None:
            raise Exception("No UCIS library is available. Do you need to adjust your init parameters?")

        return LibUCIS()
    
    def read(self, file_or_filename) -> 'UCIS':
        from ucis.lib.lib_ucis import LibUCIS
        lib = self._get_lib()
        if lib is None:
            raise Exception("No UCIS library is available. Do you need to adjust your init parameters?")
        
        return LibUCIS(file_or_filename)
    
    def write(self, db : 'UCIS', file_or_filename):
        raise NotImplementedError("DbFormatIf.write not implemented by %s" % str(type(self)))
    
    def _get_lib(self):
        pass
    
    @staticmethod
    def register(rgy):
        rgy.addDatabaseFormat(FormatDescDb(
            DbFormatIfLib,
            name="libucis",
            flags=FormatDbFlags.Create|FormatDbFlags.Read,
            description="Reads coverage data via an implementation of the UCIS C API"))
    