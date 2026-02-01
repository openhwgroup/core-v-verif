'''
Created on Apr 8, 2020

@author: ballance
'''
from ucis.report.coverage_report import CoverageReport
from typing import List

class TextCoverageReportFormatter(object):
    
    def __init__(self, 
                report : CoverageReport, 
                fp):
        self._report = report
        self._fp = fp
        self._ind = ""
        self.details = False
        self.round = 2
        self.order_bins_by_hit = False
        
    def report(self):
        for cg in self._report.covergroups:
            self.report_covergroup(cg, False)
            
    def report_covergroup(self, 
                          cg : CoverageReport.Covergroup,
                          is_inst):
        fmt = "%s %s : %." + str(self.round) + "f%%"
        self.writeln(fmt,
                "INST" if is_inst else "TYPE",
                cg.name, round(cg.coverage, self.round))
        
        with self.indent():
            for cp in cg.coverpoints:
                self.report_coverpoint(cp)
            for cr in cg.crosses:
                self.report_cross(cr)
        
            for cg_i in cg.covergroups:
                self.report_covergroup(cg_i, True)
            
    def report_coverpoint(self, cp : CoverageReport.Coverpoint):
        fmt = "CVP %s : %." + str(self.round) + "f%%"
        self.writeln(fmt, cp.name, round(cp.coverage, self.round))
        
        if self.details:
            self.writeln("Bins:")
            with self.indent():
                self.report_bins(cp.bins)
            if len(cp.ignore_bins) > 0:
                self.writeln("IgnoreBins:")
                with self.indent():
                    self.report_bins(cp.ignore_bins)
            if len(cp.illegal_bins) > 0:
                self.writeln("IllegalBins:")
                with self.indent():
                    self.report_bins(cp.illegal_bins)

    def report_cross(self, cr : CoverageReport.Cross):
        fmt = "CROSS %s : %." + str(self.round) + "f%%"
        self.writeln(fmt, cr.name, round(cr.coverage, self.round))
        
        if self.details:
            self.writeln("Bins:")
            with self.indent():
                self.report_bins(cr.bins)
        
    def report_bins(self, bins : List[CoverageReport.CoverBin]):
        if self.order_bins_by_hit:
            for b in bins:
                if b.hit:
                    self.writeln("%s : %d", b.name, b.count)
            for b in bins:
                if not b.hit:
                    self.writeln("%s : %d", b.name, b.count)
        else:
            for b in bins:
                self.writeln("%s : %d", b.name, b.count)
    
    def writeln(self, msg, *args):
        self._fp.write(self._ind + msg % args + "\n")

    def indent(self):
        return self
    
    def __enter__(self):
        self._ind += "    "
        
    def __exit__(self, t, v, tb):
        self._ind = self._ind[:-4]
        