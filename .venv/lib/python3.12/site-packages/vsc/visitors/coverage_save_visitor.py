

# Created on Mar 10, 2020
#
# @author: ballance

from enum import Enum, auto
from ucis import UCIS_HISTORYNODE_TEST, UCIS_OTHER, UCIS_DU_MODULE, \
    UCIS_ENABLED_STMT, UCIS_ENABLED_BRANCH, UCIS_ENABLED_COND, UCIS_ENABLED_EXPR, \
    UCIS_ENABLED_FSM, UCIS_ENABLED_TOGGLE, UCIS_INST_ONCE, UCIS_SCOPE_UNDER_DU, \
    UCIS_INSTANCE, UCIS_IGNOREBIN, UCIS_CVGBIN, UCIS_ILLEGALBIN
from ucis.file_handle import FileHandle
from ucis.scope import Scope
from ucis.test_data import TestData
from ucis.ucis import UCIS
from typing import Dict, List, Set

from vsc.model.covergroup_model import CovergroupModel
from vsc.model.coverpoint_bin_array_model import CoverpointBinArrayModel
from vsc.model.coverpoint_bin_collection_model import CoverpointBinCollectionModel
from vsc.model.coverpoint_model import CoverpointModel
from vsc.model.model_visitor import ModelVisitor
import os
from builtins import set
from vsc.model.coverpoint_cross_model import CoverpointCrossModel
from vsc.coverage import coverpoint


class SavePhase(Enum):
    CollectSources = auto()

class CoverageSaveVisitor(ModelVisitor):
    # Create design units (module types)
    # - 
    # Test data
    # Instance (points to design unit)
    # Create covergroup, relative to the instance hierarchy
    # - Create coverpoints
    #   - Create bins
    
    def __init__(self, db : UCIS):
        self.phase = SavePhase.CollectSources
        self.db = db
        # Map of filename -> FileHandle 
        self.file_m : Dict[str,FileHandle] = {}
        self.cg_default_du_name = "du"
        self.cg_default_inst_name = "cg_inst"
        self.logicalname = "logicalName"
        self.in_bin_collection = False
        self.active_scope_s = []
        self.cg_name_s : Set[str] = set()
        self.file_handle_m : Dict[str,FileHandle] = {}
        self.ucis_src_lang = UCIS_OTHER
        self.ucis_cwd = os.getcwd()
        self.coverpoint_m = {}

        
    def save(self, td : TestData, cg_l : List[CovergroupModel]):

        # First, go through all scopes to identify
        # the relevant source files        
        self.phase = SavePhase.CollectSources
        
        # First, create a history node. This must always
        # be provided if we're creating a bare UCIS file.
        # If we're just contributing data in the context
        # of another tool's run, this is omitted
        if td is not None:
            histnode = self.db.createHistoryNode(
                None,
                self.logicalname,
                "foo.ucis", # Why do we need to pass this in?
                UCIS_HISTORYNODE_TEST)
            histnode.setTestData(td)
        
        for cg in cg_l:
            cg.accept(self)

    def visit_covergroup(self, cg : CovergroupModel):
        from ucis.source_info import SourceInfo
        cg_inst = self.get_cg_inst(cg)
        
        cg_name = cg.name if cg.name is not None else "<unknown>"
        inst_location = None
        
        if cg.type_cg is None:
            if cg.srcinfo_decl is not None:
                fh = self.get_file_handle(cg.srcinfo_decl.filename)
                inst_location = SourceInfo(
                    fh, 
                    cg.srcinfo_decl.lineno, 
                    0)

            # obtain weight from covergroup
            # TODO: should be .options vs .type_options
            weight = cg.options.weight
            # TODO: obtain at_least from coverpoint and set on cp_scope
            # TODO: obtain goal from coverpoint and set on cp_scope
            # TODO: obtain comment from coverpoint and set on cp_scope
            self.active_scope_s.append(cg_inst.createCovergroup(
                cg_name,
                inst_location,
                weight, # weight
                UCIS_OTHER)) # Source type
        else:
            if cg.srcinfo_inst is not None:
                fh = self.get_file_handle(cg.srcinfo_inst.filename)
                inst_location = SourceInfo(
                    fh, 
                    cg.srcinfo_inst.lineno, 
                    0)
            self.active_scope_s.append(cg_inst.createCoverInstance(
                self.get_cg_instname(cg),
                inst_location,
                1, # weight
                UCIS_OTHER)) # Source type
        
        super().visit_covergroup(cg)
        self.active_scope_s.pop()
        
    def visit_coverpoint(self, cp : CoverpointModel):
        from ucis.source_info import SourceInfo
        active_s = self.active_scope_s[-1]
        
        cp_name = cp.name
        decl_location = None
        
        if cp.srcinfo_decl is not None:
            decl_location = SourceInfo(
                self.get_file_handle(cp.srcinfo_decl.filename),
                cp.srcinfo_decl.lineno, 0)
            
        # Obtain weight from coverpoint
        # TODO: obtain from .options vs .type_options?
        weight = cp.options.weight
        # TODO: obtain at_least from coverpoint and set on cp_scope
        at_least = cp.options.at_least
        # TODO: obtain goal from coverpoint and set on cp_scope
        # TODO: obtain comment from coverpoint and set on cp_scope
        cp_scope = active_s.createCoverpoint(
            cp_name,
            decl_location,
            weight, # weight
            UCIS_OTHER) # Source type
        self.coverpoint_m[cp.name] = cp_scope
        # TODO: setAtLeast()
#        cp_scope.set

        for bi in range(cp.get_n_bins()):
            decl_location = None
            bn_name = cp.get_bin_name(bi)
            cp_bin = cp_scope.createBin(
                bn_name,
                decl_location,
                at_least, # at_least
                cp.get_bin_hits(bi),
                bn_name,
                UCIS_CVGBIN)
            
        for bi in range(cp.get_n_ignore_bins()):
            decl_location = None
            bn_name = cp.get_ignore_bin_name(bi)
            cp_bin = cp_scope.createBin(
                bn_name,
                decl_location,
                at_least, # at_least
                cp.get_ignore_bin_hits(bi),
                bn_name,
                UCIS_IGNOREBIN)
            
        for bi in range(cp.get_n_illegal_bins()):
            decl_location = None
            bn_name = cp.get_illegal_bin_name(bi)
            cp_bin = cp_scope.createBin(
                bn_name,
                decl_location,
                at_least, # at_least
                cp.get_illegal_bin_hits(bi),
                bn_name,
                UCIS_ILLEGALBIN)
            
        
    def visit_coverpoint_bin_collection(self, bn:CoverpointBinCollectionModel):
        self.in_bin_collection = True
        super().visit_coverpoint_bin_collection(bn)
        self.in_bin_collection = False
        
    def visit_coverpoint_bin_array(self, bn:CoverpointBinArrayModel):
        from ucis.source_info import SourceInfo
        active_cp = self.active_scope_s[-1]
        decl_location = None
        
        if bn.srcinfo_decl is not None:
            decl_location = SourceInfo(
                self.get_file_handle(bn.srcinfo_decl.filename),
                bn.srcinfo_decl.lineno, 0)
            
        for i in range((bn.high-bn.low)+1):
            v = bn.low+i
            bn_name = bn.name + "[%d]" % (v,)
            cp_bin = active_cp.createBin(
                bn_name,
                decl_location,
                1, # weight
                bn.get_hits(i),
                bn.name
            )
            
    def visit_coverpoint_cross(self, cr:CoverpointCrossModel):
        from ucis.source_info import SourceInfo
        active_s = self.active_scope_s[-1]

        cr_name = cr.name
        decl_location = None

        # Create a list of coverpoint scopes        
        coverpoint_l = []
        for cp in cr.coverpoints():
            coverpoint_l.append(self.coverpoint_m[cp.name])
        
        if cp.srcinfo_decl is not None:
            decl_location = SourceInfo(
                self.get_file_handle(cp.srcinfo_decl.filename),
                cp.srcinfo_decl.lineno, 0)
            
        # Obtain weight from coverpoint
        # TODO: obtain from .options vs .type_options?
        weight = cr.options.weight
        # TODO: obtain at_least from coverpoint and set on cp_scope
        at_least = cr.options.at_least
        # TODO: obtain goal from coverpoint and set on cp_scope
        # TODO: obtain comment from coverpoint and set on cp_scope
        cr_scope = active_s.createCross(
            cr_name,
            decl_location,
            weight, # weight
            UCIS_OTHER,
            coverpoint_l) # Source type
        # TODO: setAtLeast()
#        cp_scope.set

        for bi in range(cr.get_n_bins()):
            decl_location = None
            bn_name = cr.get_bin_name(bi)
            cr_bin = cr_scope.createBin(
                bn_name,
                decl_location,
                at_least,
                cr.get_bin_hits(bi),
                bn_name)        
            
    def get_cg_instname(self, cg : CovergroupModel)->str:
        iname = None
        
        if cg.instname is not None:
            iname = cg.instname
        else:
            iname = cg.name

        for i in range(1000):
            if i == 0:
                if not iname in self.cg_name_s:
                    self.cg_name_s.add(iname)
                    break
            else:
                if not "%s_%d" % (iname,i) in self.cg_name_s:
                    iname = "%s_%d" % (iname,i)
                    self.cg_name_s.add(iname)
                    break

        return iname
        
    def get_cg_inst(self, cg : CovergroupModel) -> Scope:
        if len(self.active_scope_s) > 0:
            return self.active_scope_s[-1]
        else:
            # Need to create a default scope
#            from ucis.source_info import SourceInfo
#            file = self.db.createFileHandle("dummy", os.getcwd())
#            du_src_info = SourceInfo(file, 0, 0)
            du_src_info = None
            
            cg_default_du = self.db.createScope(
                self.cg_default_du_name,
                du_src_info,
                1, # weight
                UCIS_OTHER, # source language
                UCIS_DU_MODULE,
                UCIS_ENABLED_STMT | UCIS_ENABLED_BRANCH
                | UCIS_ENABLED_COND | UCIS_ENABLED_EXPR
                | UCIS_ENABLED_FSM | UCIS_ENABLED_TOGGLE
                | UCIS_INST_ONCE | UCIS_SCOPE_UNDER_DU)
            
            cg_default_inst = self.db.createInstance(
                self.cg_default_inst_name,
                None, # sourceinfo
                1, # weight
                UCIS_OTHER, # source language
                UCIS_INSTANCE,
                cg_default_du,
                UCIS_INST_ONCE)

            self.active_scope_s.append(cg_default_inst)
            
            return cg_default_inst
        
    def get_file_handle(self, path):
        fh = None
        if path in self.file_handle_m.keys():
            fh = self.file_handle_m[path]
        else:
            fh = self.db.createFileHandle(path, self.ucis_cwd)
            self.file_handle_m[path] = fh
        return fh

    