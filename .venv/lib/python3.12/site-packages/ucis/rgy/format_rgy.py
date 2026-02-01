'''
Created on Jun 22, 2022

@author: mballance
'''
from typing import Dict
from .format_if_db import FormatDescDb
from ucis.rgy.format_if_rpt import FormatDescRpt
from ucis.report.format_rpt_text import FormatRptText
from ucis.report.format_rpt_json import FormatRptJson
from ucis.xml.db_format_if_xml import DbFormatIfXml
from ucis.lib.db_format_if_lib import DbFormatIfLib
from ucis.yaml.db_format_if_yaml import DbFormatIfYaml

class FormatRgy(object):
    """
    Registry for various format-support objects. Classes to access
    coverage databases and emit reports are registered here.
    """

    _in_inst = False    
    _inst = None
    
    def __init__(self):
        if not FormatRgy._in_inst:
            raise Exception("Obtain the FormatRgy singleton by calling FormatRgy.inst()")
        self._format_db_m : Dict[str, FormatDescDb] = {}
        self._format_rpt_m : Dict[str, FormatDescRpt] = {}
        pass
    
    def addDatabaseFormat(self, desc : FormatDescDb):
        self._format_db_m[desc._name] = desc
    
    def addReportFormat(self, desc : FormatDescRpt):
        self._format_rpt_m[desc._name] = desc
    
    def getDatabaseFormats(self):
        fmts = list(self._format_db_m.keys())
        fmts.sort()
        return fmts
    
    def hasDatabaseFormat(self, fmt):
        return fmt in self._format_db_m.keys()
    
    def hasReportFormat(self, fmt):
        return fmt in self._format_rpt_m.keys()
    
    def getReportFormats(self):
        fmts = list(self._format_rpt_m.keys())
        fmts.sort()
        return fmts
    
    def getDatabaseDesc(self, fmt):
        return self._format_db_m[fmt]
    
    def getReportDesc(self, fmt):
        return self._format_rpt_m[fmt]
    
    def getDefaultDatabase(self):
        return 'xml'
    
    def getDefaultReport(self):
        return 'txt'
    
    def _init_rgy(self):
#        self.addDatabaseFormat(FormatDescDb(
#            fmt_if, name, flags, description))
        DbFormatIfXml.register(self)
        DbFormatIfLib.register(self)
        DbFormatIfYaml.register(self)
        
        FormatRptJson.register(self)
        FormatRptText.register(self)
    
    @classmethod
    def inst(cls):
        if cls._inst is None:
            cls._in_inst = True
            cls._inst = cls()
            cls._in_inst = False
            cls._inst._init_rgy()
        return cls._inst
    
    