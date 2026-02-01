'''
Created on Jul 3, 2021

@author: mballance
'''
from vsc.model.source_info import SourceInfo
import time
from vsc.profile.solve_info import SolveInfo

class Profiler(object):
    
    class Info(object):

        def __init__(self, tag):
            self.tag = tag
            self.count = 0
            self.totaltime = 0
            
            self.n_sat_calls = 0
            self.min_sat_calls = (1 << 32)
            self.max_sat_calls = 0
            
            self.mintime = (1 << 32)
            self.maxtime = 0
            self.n_randsets = 0
            self.n_cfields  = 0
    
    _inst = None
    
    def __init__(self):
        self.type_m = {}
        self.loc_m = {}
        self.depth = 0
        self.start = -1
        self.active = None
    
    @classmethod
    def inst(cls):
        if cls._inst is None:
            cls._inst = Profiler()
        return cls._inst
    
    def show_profile(self, out):
        out.write("RandSites:\n")
        for key in sorted(self.loc_m.keys()):
            info = self.loc_m[key]
            out.write("    \"%s\":\n" % info.tag)
            out.write("      count: %d\n" % info.count)
            out.write("      randinfo:\n")
            out.write("        sets: %d\n" % info.n_randsets)
            out.write("        cfields: %d\n" % info.n_cfields)
            out.write("      time: %d\n" % info.totaltime)
            out.write("        min: %d\n" % info.mintime)
            out.write("        max: %d\n" % info.maxtime)
            out.write("        avg: %d\n" % int(info.totaltime/info.count))
            out.write("      sat-calls: %d\n" % info.n_sat_calls)
            out.write("        min: %d\n" % info.min_sat_calls)
            out.write("        max: %d\n" % info.max_sat_calls)
            out.write("        avg: %d\n" % int(info.n_sat_calls / info.count))
        pass
    
    def randomize_start(self, srcinfo : SourceInfo, field_l, constraint_l):
        if self.depth == 0:
            self.start = int(round(time.time() * 1000))
            if len(field_l) == 1:
                # Type-based randomization
#                print("randomize type %s" % field_l[0].typename)
                loctag = "%s:%d" % (srcinfo.filename, srcinfo.lineno)
            
                if loctag not in self.loc_m.keys():
                    self.loc_m[loctag] = Profiler.Info("%s @ %s" % (
                        field_l[0].typename, loctag))
                self.active = self.loc_m[loctag]
            elif len(field_l) == 1 and constraint_l is not None:
                loctag = "%s:%d" % (srcinfo.filename, srcinfo.lineno)
            
                if loctag not in self.loc_m.keys():
                    self.loc_m[loctag] = Profiler.Info("%s @ %s" % (
                        field_l[0].typename, loctag))
                self.active = self.loc_m[loctag]
            else:
                # Site-based randomization
                pass
        self.depth += 1
    
    def randomize_done(self, srcinfo, solve_info : SolveInfo):
        
        if self.depth == 1:
            end = int(round(time.time() * 1000))
            
            if self.active is not None:
                total = end - self.start
                self.active.totaltime += total
                self.active.n_randsets = solve_info.n_randsets
                self.active.n_cfields  = solve_info.n_cfields
                self.active.n_sat_calls += solve_info.n_sat_calls
                
                if total > self.active.maxtime:
                    self.active.maxtime = total
                if total < self.active.mintime:
                    self.active.mintime = total
                    
                if solve_info.n_sat_calls < self.active.min_sat_calls:
                    self.active.min_sat_calls = solve_info.n_sat_calls
                if solve_info.n_sat_calls > self.active.max_sat_calls:
                    self.active.max_sat_calls = solve_info.n_sat_calls
                    
                self.active.count += 1
                pass
            
            self.active = None
            
        self.depth -= 1
        pass
    