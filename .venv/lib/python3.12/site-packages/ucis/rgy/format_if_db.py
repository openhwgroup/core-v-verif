'''
Created on Jun 11, 2022

@author: mballance
'''
from ucis.ucis import UCIS
from enum import IntFlag, auto

class FormatDbFlags(IntFlag):
    Create = auto()
    Read = auto()
    Write = auto()
    
class FormatDescDb(object):
    
    def __init__(self, 
                 fmt_if : 'FormatIfDb',
                 name : str,
                 flags : FormatDbFlags,
                 description : str):
        self._fmt_if = fmt_if
        self._name = name
        self._flags = flags
        self._description = description
        
    @property
    def fmt_if(self):
        return self._fmt_if
    
    @property
    def name(self):
        return self._name
    
    @property
    def flags(self):
        return self._flags
    
    @property
    def description(self):
        return self._description


class FormatIfDb(object):
    
    def init(self, options):
        raise NotImplementedError("DbFormatIf.init not implemented by %s" % str(type(self)))
    
    def create(self, filename=None) -> UCIS:
        """
        Creates a new UCIS database.
        If filename is None, the database will be created in memory. Some database
        backends can take advantage of the filename to write directly to disk instead
        of later copying to disk. Databases that can write directly to disk will
        overwrite any existing file on creation.
        """
        raise NotImplementedError("DbFormatIf.create not implemented by %s" % str(type(self)))
    
    def read(self, file_or_filename) -> UCIS:
        """
        Read a UCIS database from a file
        """
        raise NotImplementedError("DbFormatIf.read not implemented by %s" % str(type(self)))
    
