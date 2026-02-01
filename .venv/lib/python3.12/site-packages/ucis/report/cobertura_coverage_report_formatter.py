'''
Created on Apr 8, 2020

@author: ballance
'''
from vsc.report.coverage_report import CoverageReport

class CoberturaCoverageReportFormatter(object):
    
    def __init__(self, report : CoverageReport, fp):
        self._report = report
        self._fp = fp
        pass
    
    
    def format(self):
        
        pass
    