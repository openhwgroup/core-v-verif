'''
Created on Mar 27, 2020

@author: ballance
'''
from ucis.scope_type_t import ScopeTypeT
from ucis.report.coverage_report import CoverageReport
from ucis.coverpoint import Coverpoint
from ucis.cover_type_t import CoverTypeT
from math import ceil
from ucis.cross import Cross


class CoverageReportBuilder(object):
    """
    Builds a coverage-report object from a UCIS database
    """
    
    def __init__(self, db):
        self.db = db
        self.report = CoverageReport()
    
    @staticmethod
    def build(db : 'UCIS') ->'CoverageReport':
        """
        Builds a CoverageReport object from a UCIS database
        """
        
        builder = CoverageReportBuilder(db)
        return builder._build()
        

    def _build(self)->'CoverageReport':
        
        for iscope in self.db.scopes(ScopeTypeT.INSTANCE):
            self.build_covergroups(iscope)
            
        return self.report
            

    def build_covergroups(self, iscope):
        
        coverage = 0.0
        div = 0
        
        for cg_t in iscope.scopes(ScopeTypeT.COVERGROUP):
            cg = self.build_covergroup(cg_t)
            if cg.weight > 0:
                coverage += cg.coverage * cg.weight
            div += cg.weight
            self.report.covergroups.append(cg)
            self.report.covergroup_m[cg.instname] = cg
        self.report.coverage = coverage/div
            
    def build_covergroup(self, cg_n)->CoverageReport.Covergroup:
        cg_r = CoverageReport.Covergroup(
            cg_n.getScopeName(),
            cg_n.getScopeName())
        
        cg_r.weight = cg_n.getWeight()
        
        for cp_in in cg_n.scopes(ScopeTypeT.COVERPOINT):
            cg_r.coverpoints.append(self.build_coverpoint(cp_in))
            
        for cr_in in cg_n.scopes(ScopeTypeT.CROSS):
            cg_r.crosses.append(self.build_cross(cr_in))

        for cg_in in cg_n.scopes(ScopeTypeT.COVERINSTANCE):
            cg_r.covergroups.append(self.build_covergroup(cg_in))
            
        # Determine the covergroup coverage
        coverage = 0.0

        div = 0
        for cp in cg_r.coverpoints:
            if cp.weight > 0:
                coverage += cp.coverage * cp.weight
            div += cp.weight
            
        for cr in cg_r.crosses:
            coverage += cr.coverage * cr.weight
            div += cr.weight
            
        if div > 0: coverage /= div

        cg_r.coverage = coverage
        
        return cg_r

    def build_coverpoint(self, cp_n : Coverpoint):
        cp_r = CoverageReport.Coverpoint(cp_n.getScopeName())
        cp_r.weight = cp_n.getWeight()
        
        # Read in bins
        num_hit = 0
        total = 0
        for ci_n in cp_n.coverItems(CoverTypeT.CVGBIN):
            cvg_data = ci_n.getCoverData()
            
            if cvg_data.data >= cvg_data.at_least:
                num_hit += 1
                
            cp_r.bins.append(CoverageReport.CoverBin(
                    ci_n.getName(),
                    cvg_data.at_least,
                    cvg_data.data))

            total += 1
            
        for ci_n in cp_n.coverItems(CoverTypeT.IGNOREBIN):
            cvg_data = ci_n.getCoverData()
            
            cp_r.ignore_bins.append(CoverageReport.CoverBin(
                    ci_n.getName(),
                    cvg_data.at_least,
                    cvg_data.data))
            
        for ci_n in cp_n.coverItems(CoverTypeT.ILLEGALBIN):
            cvg_data = ci_n.getCoverData()
            
            cp_r.illegal_bins.append(CoverageReport.CoverBin(
                    ci_n.getName(),
                    cvg_data.at_least,
                    cvg_data.data))

        if total > 0:
            cp_r.coverage = (100*num_hit)/total
        else:
            cp_r.coverage = 0
        
        return cp_r
        

    def build_cross(self, cr_n : Cross):
        cr_r = CoverageReport.Cross(cr_n.getScopeName())
        
        # Read in bins
        num_hit = 0
        total = 0
        for ci_n in cr_n.coverItems(CoverTypeT.CVGBIN):
            cvg_data = ci_n.getCoverData()

            if cvg_data.data >= cvg_data.at_least:
                num_hit += 1
                
            cr_r.bins.append(CoverageReport.CoverBin(
                    ci_n.getName(),
                    cvg_data.goal,
                    cvg_data.data))

            total += 1

        if total > 0: cr_r.coverage = (100*num_hit)/total
        
        return cr_r        
        
        
    
    