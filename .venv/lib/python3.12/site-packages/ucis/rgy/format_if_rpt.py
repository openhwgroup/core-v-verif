'''
Created on Jun 22, 2022

@author: mballance
'''
from ucis.ucis import UCIS
from enum import IntFlag, auto

class FormatRptOutFlags(IntFlag):
    Stream = auto()
    Dir = auto()

class FormatDescRpt(object):
    
    def __init__(self, 
                 fmt_if : 'FormatIfDb',
                 name : str,
                 out_flags : FormatRptOutFlags,
                 description : str):
        self._fmt_if = fmt_if
        self._name = name
        self._out_flags = out_flags
        self._description = description
        
    @property
    def fmt_if(self):
        return self._fmt_if

    @property
    def name(self):
        return self._name

    @property
    def out_flags(self):
        return self._out_flags
    
    @property
    def description(self):
        return self._description

class FormatIfRpt(object):
    
    def report(self, 
               db : UCIS,
               out,
               args):
        raise NotImplementedError("FormatIfRpt.report not implemented by %s" % str(type(self)))
    