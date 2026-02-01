'''
Created on Nov 9, 2021

@author: mballance
'''
import yaml

from io import StringIO
from ucis.cover_type_t import CoverTypeT
from ucis.flags_t import FlagsT
from ucis.mem.mem_ucis import MemUCIS
from ucis.scope import Scope
from ucis.scope_type_t import ScopeTypeT
from ucis.source_t import SourceT
from ucis.ucis import UCIS

import os
import json
import python_jsonschema_objects as pjs
import yaml
from yaml.loader import Loader
import jsonschema


class YamlReader(object):
    
    def __init__(self):
        self.active_scope_s = []
        self.cg_default_du_name = "du"
        self.cg_default_inst_name = "cg_inst"
        self.cg_default_du = None
        self.cvg_ns = None
        pass
    
    _coverage_ns = None
    _coverage_schema = None
    
    @classmethod
    def getCoverageNS(cls):
        if cls._coverage_ns is None:
            schema = cls.getCoverageSchema()
            builder = pjs.ObjectBuilder(schema)
            cls._coverage_ns = builder.build_classes()
        return cls._coverage_ns
    
    @classmethod
    def getCoverageSchema(cls):
        if cls._coverage_schema is None:
            yaml_dir = os.path.dirname(os.path.abspath(__file__))
            schema_dir = os.path.join(os.path.dirname(yaml_dir), "schema")

            with open(os.path.join(schema_dir, "coverage.json"), "r") as fp:
                cls._coverage_schema = json.load(fp)
        return cls._coverage_schema
            
    
    def loads(self, s) -> UCIS:
        fp = StringIO(s)

        return self.load(fp)

    def load(self, fp) -> UCIS:
        
        self.cvg_ns = YamlReader.getCoverageNS()
        schema = YamlReader.getCoverageSchema()

        cov_yml = yaml.load(fp, Loader=yaml.FullLoader)
        
        jsonschema.validate(instance=cov_yml, schema=schema)
            
        coverage = self.cvg_ns.CoverageData()
        coverage = coverage.from_json(json.dumps(cov_yml))
        
        self.db = MemUCIS()

        # Create root scopes
        du_src_info = None
            
        self.cg_default_du = self.db.createScope(
            self.cg_default_du_name,
            du_src_info,
            1, # weight
            SourceT.OTHER, # source language
            ScopeTypeT.DU_MODULE,
            FlagsT.ENABLED_STMT | FlagsT.ENABLED_BRANCH
            | FlagsT.ENABLED_COND | FlagsT.ENABLED_EXPR
            | FlagsT.ENABLED_FSM | FlagsT.ENABLED_TOGGLE
            | FlagsT.INST_ONCE | FlagsT.SCOPE_UNDER_DU)
            
        self.cg_default_inst = self.db.createInstance(
            self.cg_default_inst_name,
            None, # sourceinfo
            1, # weight
            SourceT.OTHER, # source language
            ScopeTypeT.INSTANCE,
            self.cg_default_du,
            FlagsT.INST_ONCE)

        coverage = coverage.coverage
        
        if coverage.covergroups is not None:
            for cg_t in coverage.covergroups:
                self.process_covergroup(cg_t)
                
        return self.db
                
                
    def process_covergroup(self, cg_t):
        
        cg_location = None
            
        weight = 1
        if cg_t.weight is not None:
            weight = int(cg_t.weight)

        # Create type coverage from instance data
        cp_t_l = []
        cp_t_m = {}
        cr_t_l = []
        # Map of string to tuple of cross,binmap
        cr_t_m = {}
        if cg_t.instances is not None:
            for cg_i in cg_t.instances:
                if cg_i.coverpoints is not None:
                    for cp in cg_i.coverpoints:
                        if str(cp.name) not in cp_t_m.keys():
                            cp_t = self.cvg_ns.Coverpoint()
                            cp_t.name = str(cp.name)
                            cp_t_m[cp_t.name] = cp_t
                            cp_t_l.append(cp_t)
                        else:
                            cp_t = cp_t_m[str(cp.name)]
                            
                        # Now, do bins...
                        if cp.bins is not None:
                            if cp_t.bins is None:
                                cp_t.bins = []
                            for b in cp.bins:
                                # Find the 'type' version
                                t_b = None
                                for t_b_t in cp_t.bins:
                                    if t_b_t.name == b.name:
                                        t_b = t_b_t
                                        break
                                if t_b is None:
                                    t_b = self.cvg_ns.CoverageBin()
                                    t_b.name = str(b.name)
                                    t_b.count = 0
                                    cp_t.bins.append(t_b)
                                t_b.count += b.count
                                
                        if cp.ignorebins is not None:
                            if cp_t.ignorebins is None:
                                cp_t.ignorebins = []
                            for b in cp.ignorebins:
                                # Find the 'type' version
                                t_b = None
                                for t_b_t in cp_t.ignorebins:
                                    if t_b_t.name == b.name:
                                        t_b = t_b_t
                                        break
                                if t_b is None:
                                    t_b = self.cvg_ns.CoverageBin()
                                    t_b.name = str(b.name)
                                    t_b.count = 0
                                    cp_t.bins.append(t_b)
                                t_b.count += b.count
                                
                        if cp.illegalbins is not None:
                            if cp_t.illegalbins is None:
                                cp_t.illegalbins = []
                            for b in cp.illegalbins:
                                # Find the 'type' version
                                t_b = None
                                for t_b_t in cp_t.illegalbins:
                                    if t_b_t.name == b.name:
                                        t_b = t_b_t
                                        break
                                if t_b is None:
                                    t_b = self.cvg_ns.CoverageBin()
                                    t_b.name = str(b.name)
                                    t_b.count = 0
                                    cp_t.bins.append(t_b)
                                t_b.count += b.count
                        
                if cg_i.crosses is not None:
                    for cr in cg_i.crosses:
                        if cr.coverpoints is None:
                            raise Exception("Cross %s in covergroup instance %s doesn't specify coverpoints" % (
                                str(cr.name), str(cg_i.name)))
                        if str(cr.name) not in cr_t_m.keys():
                            cr_t = self.cvg_ns.Cross()
                            cr_t.name = str(cr.name)
                            cr_t.coverpoints = []
                            for cr_cp in cr.coverpoints:
                                cr_t.coverpoints.append(cr_cp)
                            cr_t_bins_m = {}
                            cr_t_m[str(cr.name)] = (cr_t, cr_t_bins_m)
                            cr_t_l.append(cr_t)
                            
                            if cr.bins is not None:
                                cr_t.bins = []
                        else:
                            cr_t = cr_t_m[str(cr.name)][0]
                            cr_t_bins_m = cr_t_m[str(cr.name)][1]
                            
                        # Now, proceed to aggregate bins
                        if cr.bins is not None:
                            for b in cr.bins:
                                if b.name in cr_t_bins_m.keys():
                                    cr_t_bins_m[str(b.name)].count += b.count
                                else:
                                    b_t = self.cvg_ns.CoverageBin()
                                    b_t.name = str(b.name)
                                    b_t.count = b.count
                                    cr_t.bins.append(b_t)
                                    cr_t_bins_m[str(b.name)] = b_t
                
        else:
            print("Warning: Covergroup type %s has no instances" % str(cg_t.name))

        # Now, convert to UCIS
        cg_t_scope = self.cg_default_inst.createCovergroup(
            str(cg_t.name),
            cg_location,
            weight,
            SourceT.OTHER)
        
        cp_n_scope_m = {}
        
        # Create type coverpoints and crosses
        for cp in cp_t_l:
            cp_n_scope_m[str(cp.name)] = self.record_coverpoint(cg_t_scope, cp)
            
        for cr in cr_t_l:
            cp_l = []
            
            for cp in cr.coverpoints:
                if cp in cp_n_scope_m.keys():
                    cp_l.append(cp_n_scope_m[cp])
                else:
                    raise Exception("Coverpoint %s referenced in cross %s is not defined" % (
                        cp, str(cr.name)))
            
            self.record_cross(cg_t_scope, cp_l, cr)

        # Now, write out instances
        cp_n_scope_m = {}
        for i in cg_t.instances:
            cg_i_scope = cg_t_scope.createCoverInstance(
                str(i.name),
                cg_location,
                weight,
                SourceT.OTHER)

            if i.coverpoints is not None:            
                for cp in i.coverpoints:
                    cp_n_scope_m[str(cp.name)] = self.record_coverpoint(cg_i_scope, cp)
                    
            if i.crosses is not None:
                for cr in i.crosses:
                    cp_l = []
            
                    for cp in cr.coverpoints:
                        if cp in cp_n_scope_m.keys():
                            cp_l.append(cp_n_scope_m[cp])
                        else:
                            raise Exception("Coverpoint %s referenced in cross %s is not defined" % (
                                cp, str(cr.name)))
                            
                    self.record_cross(cg_i_scope, cp_l, cr)

    def record_coverpoint(self, cp_parent_s, cp):
        
        cp_location = None
        
        weight = 1
#        if "weight" in cp_s.keys():
#            weight = int(cp_s["weight"])
            
        at_least = 1
        if cp.atleast is not None:
            at_least = cp.atleast
            
        cp_scope = cp_parent_s.createCoverpoint(
            str(cp.name),
            cp_location,
            weight,
            SourceT.OTHER)

        if cp.bins is not None:        
            for b in cp.bins:
                cp_scope.createBin(
                    str(b.name),
                    cp_location,
                    at_least,
                    b.count,
                    str(b.name),
                    CoverTypeT.CVGBIN)
                
        if cp.ignorebins is not None:
            for b in cp.ignorebins:
                cp_scope.createBin(
                    str(b.name),
                    cp_location,
                    at_least,
                    b.count,
                    str(b.name),
                    CoverTypeT.IGNOREBIN)
                
        if cp.illegalbins is not None:
            for b in cp.illegalbins:
                cp_scope.createBin(
                    str(b.name),
                    cp_location,
                    at_least,
                    b.count,
                    str(b.name),
                    CoverTypeT.ILLEGALBIN)
                
        return cp_scope
                
    def record_cross(self, cp_parent_s, cp_l, cr):
        cr_location = None
        
        weight = 1
#        if "weight" in cp_s.keys():
#            weight = int(cp_s["weight"])
            
        at_least = 1
        if cr.atleast is not None:
            at_least = cr.atleast
            
        cr_scope = cp_parent_s.createCross(
            str(cr.name),
            cr_location,
            weight,
            SourceT.OTHER,
            cp_l)

        if cr.bins is not None:        
            for b in cr.bins:
                cr_scope.createBin(
                    str(b.name),
                    cr_location,
                    at_least,
                    b.count,
                    str(b.name))
                    
        return cr_scope
