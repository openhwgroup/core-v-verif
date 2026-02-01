# Licensed to the Apache Software Foundation (ASF) under one
# or more contributor license agreements.  See the NOTICE file
# distributed with this work for additional information
# regarding copyright ownership.  The ASF licenses this file
# to you under the Apache License, Version 2.0 (the
# "License"); you may not use this file except in compliance
# with the License.  You may obtain a copy of the License at
#
#  http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing,
# software distributed under the License is distributed on an
# "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
# KIND, either express or implied.  See the License for the
# specific language governing permissions and limitations
# under the License.

# Created on Jan 21, 2020
#
# @author: ballance


import random
import sys
import time
from typing import List, Dict

from pyboolector import Boolector, BoolectorNode
import pyboolector
from vsc.constraints import constraint, soft
from vsc.model.bin_expr_type import BinExprType
from vsc.model.constraint_model import ConstraintModel
from vsc.model.constraint_soft_model import ConstraintSoftModel
from vsc.model.expr_bin_model import ExprBinModel
from vsc.model.expr_fieldref_model import ExprFieldRefModel
from vsc.model.expr_literal_model import ExprLiteralModel
from vsc.model.expr_model import ExprModel
from vsc.model.field_model import FieldModel
from vsc.model.field_scalar_model import FieldScalarModel
from vsc.model.model_visitor import ModelVisitor
from vsc.model.rand_if import RandIF
from vsc.model.rand_info import RandInfo
from vsc.model.rand_info_builder import RandInfoBuilder
from vsc.model.variable_bound_model import VariableBoundModel
from vsc.visitors.array_constraint_builder import ArrayConstraintBuilder
from vsc.visitors.constraint_override_rollback_visitor import ConstraintOverrideRollbackVisitor
from vsc.visitors.dist_constraint_builder import DistConstraintBuilder
from vsc.visitors.model_pretty_printer import ModelPrettyPrinter
from vsc.visitors.variable_bound_visitor import VariableBoundVisitor
from vsc.visitors.dynamic_expr_reset_visitor import DynamicExprResetVisitor
from vsc.model.solve_failure import SolveFailure
from vsc.visitors.ref_fields_postrand_visitor import RefFieldsPostRandVisitor
from vsc.model.rand_set_node_builder import RandSetNodeBuilder
from vsc.model.rand_set_dispose_visitor import RandSetDisposeVisitor
from vsc.visitors.clear_soft_priority_visitor import ClearSoftPriorityVisitor
from vsc.profile import randomize_start, randomize_done, profile_on
from vsc.model.source_info import SourceInfo
from vsc.profile.solve_info import SolveInfo
from vsc.visitors.lint_visitor import LintVisitor
from pip._internal.cli.cmdoptions import src
from vsc.model.solvegroup_swizzler_range import SolveGroupSwizzlerRange
from vsc.model.solvegroup_swizzler_partsel import SolveGroupSwizzlerPartsel
from vsc.impl.ctor import glbl_debug, glbl_solvefail_debug


class Randomizer(RandIF):
    """Implements the core randomization algorithm"""
    
    EN_DEBUG = False
    
    def __init__(self, randstate, debug=0, lint=0, solve_fail_debug=0, solve_info=None):
        self.randstate = randstate
        self.pretty_printer = ModelPrettyPrinter()
        self.solve_info = solve_info
        self.debug = debug
        if glbl_debug > 0 and glbl_debug > debug:
            self.debug = glbl_debug

        self.lint = lint
        self.solve_fail_debug = solve_fail_debug
        if glbl_solvefail_debug > 0 and glbl_solvefail_debug > solve_fail_debug:
            self.solve_fail_debug = glbl_solvefail_debug
            
#        self.swizzler = SolveGroupSwizzlerRange(solve_info)
        self.swizzler = SolveGroupSwizzlerPartsel(randstate, solve_info)
    
    _state_p = [0,1]
    _rng = None
    
    def randomize(self, ri : RandInfo, bound_m : Dict[FieldModel,VariableBoundModel]):
        """Randomize the variables and constraints in a RandInfo collection"""
        
        if self.solve_info is not None:
            self.solve_info.n_randsets = len(ri.randsets())
        
        if self.debug > 0:
            rs_i = 0
            while rs_i < len(ri.randsets()):
                rs = ri.randsets()[rs_i]
                print("RandSet[%d]" % rs_i)
                for f in rs.all_fields():
                    if f in bound_m.keys():
                        print("  Field: %s is_rand=%s %s" % (f.fullname, str(f.is_used_rand), str(bound_m[f].domain.range_l)))
                    else:
                        print("  Field: %s is_rand=%s (unbounded)" % (f.fullname, str(f.is_used_rand)))
                        
                for c in rs.constraints():
                    print("  Constraint: " + self.pretty_printer.do_print(c, show_exp=True))
                for c in rs.soft_constraints():
                    print("  SoftConstraint: " + self.pretty_printer.do_print(c, show_exp=True))
                    
                rs_i += 1
                    
            for uf in ri.unconstrained():
                print("Unconstrained: " + uf.fullname)
               
        # Assign values to the unconstrained fields first
        uc_rand = list(filter(lambda f:f.is_used_rand, ri.unconstrained()))
        for uf in uc_rand:
            if self.debug > 0:
                print("Randomizing unconstrained: " + uf.fullname)
            bounds = bound_m[uf]
            range_l = bounds.domain.range_l
            
            if len(range_l) == 1:
                # Single (likely domain-based) range
                uf.set_val(
                    self.randint(range_l[0][0], range_l[0][1]))
            else:
                # Most likely an enumerated type
                # TODO: are there any cases where these could be ranges?
                idx = self.randint(0, len(range_l)-1)
                uf.set_val(range_l[idx][0])                
                
            # Lock so we don't overwrite
            uf.set_used_rand(False)

        rs_i = 0
        start_rs_i = 0
#        max_fields = 20
        max_fields = 0
        while rs_i < len(ri.randsets()):
            btor = Boolector()
            self.btor = btor
            btor.Set_opt(pyboolector.BTOR_OPT_INCREMENTAL, True)
            btor.Set_opt(pyboolector.BTOR_OPT_MODEL_GEN, True)
            
            start_rs_i = rs_i

            constraint_l = []
            soft_constraint_l = []
            
            # Collect up to max_fields fields to randomize at a time
            n_fields = 0
            while rs_i < len(ri.randsets()):
                rs = ri.randsets()[rs_i]
                
                rs_node_builder = RandSetNodeBuilder(btor)

                all_fields = rs.all_fields()
                if self.debug > 0:
                    print("Pre-Randomize: RandSet[%d]" % rs_i)
                    for f in all_fields:
                        if f in bound_m.keys():
                            print("  Field: %s is_rand=%s %s var=%s" % (f.fullname, str(f.is_used_rand), str(bound_m[f].domain.range_l), str(f.var)))
                        else:
                            print("  Field: %s is_rand=%s (unbounded)" % (f.fullname, str(f.is_used_rand)))
                    for c in rs.constraints():
                        print("  Constraint: " + self.pretty_printer.do_print(c, show_exp=True, print_values=True))
                    for c in rs.soft_constraints():
                        print("  SoftConstraint: " + self.pretty_printer.do_print(c, show_exp=True, print_values=True))
                        
                if self.solve_info is not None:
                    self.solve_info.n_cfields += len(all_fields)

                rs_node_builder.build(rs)
                n_fields += len(all_fields)
                
#                constraint_l.extend(list(map(lambda c:(c,c.build(btor),isinstance(c,ConstraintSoftModel)), rs.constraints())))
                constraint_l.extend(list(map(lambda c:(c,c.build(btor)), rs.constraints())))
                soft_constraint_l.extend(list(map(lambda c:(c,c.build(btor)), rs.soft_constraints())))
                
                # Sort the list in descending order so we know which constraints
                # to prioritize
                soft_constraint_l.sort(key=lambda c:c[0].priority, reverse=True)
                
                rs_i += 1
                if n_fields > max_fields or rs.order != -1:
                    break
                
            for c in constraint_l:
                try:
                    btor.Assume(c[1])
                except Exception as e:
                    print("Exception: " + self.pretty_printer.print(c[0]))
                    raise e
                
            if self.solve_info is not None:
                self.solve_info.n_sat_calls += 1
                
            if btor.Sat() != btor.SAT:
                # If the system doesn't solve with hard constraints added,
                # then we may as well bail now
                active_randsets = []
                for rs in ri.randsets():
                    active_randsets.append(rs)
                    for f in rs.all_fields():
                        f.dispose()
                        
                if self.solve_fail_debug > 0:
                    raise SolveFailure(
                        "solve failure",
                        self.create_diagnostics(active_randsets))
                else:
                    raise SolveFailure(
                        "solve failure",
                        "Solve failure: set 'solve_fail_debug=1' for more details")
            else:
                # Lock down the hard constraints that are confirmed
                # to be valid
                for c in constraint_l:
                    btor.Assert(c[1])

            # If there are soft constraints, add these now
            if len(soft_constraint_l) > 0:                
                for c in soft_constraint_l:
                    try:
                        btor.Assume(c[1])
                    except Exception as e:
                        from ..visitors.model_pretty_printer import ModelPrettyPrinter
                        print("Exception: " + ModelPrettyPrinter.print(c[0]))
                        raise e

                if self.solve_info is not None:
                    self.solve_info.n_sat_calls += 1                    
                if btor.Sat() != btor.SAT:
                    # All the soft constraints cannot be satisfied. We'll need to
                    # add them incrementally
                    if self.debug > 0:
                        print("Note: some of the %d soft constraints could not be satisfied" % len(soft_constraint_l))
                        
                    for c in soft_constraint_l:
                        btor.Assume(c[1])
                        
                        if self.solve_info is not None:
                            self.solve_info.n_sat_calls += 1                    
                        if btor.Sat() == btor.SAT:
                            if self.debug > 0:
                                print("Note: soft constraint %s (%d) passed" % (
                                    self.pretty_printer.print(c[0]), c[0].priority))
                            btor.Assert(c[1])
                        else:
                            if self.debug > 0:
                                print("Note: soft constraint %s (%d) failed" % (
                                    self.pretty_printer.print(c[0]), c[0].priority))
                else:
                    # All the soft constraints could be satisfied. Assert them now
                    if self.debug > 0:
                        print("Note: all %d soft constraints could be satisfied" % len(soft_constraint_l))
                    for c in soft_constraint_l:
                        btor.Assert(c[1])
                
#            btor.Sat()
            x = start_rs_i
            while x < rs_i:
                self.swizzler.swizzle(
                    btor,
                    ri.randsets()[x],
                    bound_m)
                x += 1
                
            # Finalize the value of the field
            x = start_rs_i
            reset_v = DynamicExprResetVisitor()
            while x < rs_i:
                rs = ri.randsets()[x]
                for f in rs.all_fields():
                    f.post_randomize()
                    f.set_used_rand(False, 0)
                    f.dispose() # Get rid of the solver var, since we're done with it
                    f.accept(reset_v)
#                for f in rs.nontarget_field_s:
#                    f.dispose()
                for c in rs.constraints():
                    c.accept(reset_v)
                RandSetDisposeVisitor().dispose(rs)
                
                if self.debug > 0:
                    print("Post-Randomize: RandSet[%d]" % x)
                    for f in all_fields:
                        if f in bound_m.keys():
                            print("  Field: %s %s" % (f.fullname, str(f.val.val)))
                        else:
                            print("  Field: %s (unbounded) %s" % (f.fullname, str(f.val.val)))
                                  
                    for c in rs.constraints():
                        print("  Constraint: " + self.pretty_printer.do_print(c, show_exp=True, print_values=True))
                    for c in rs.soft_constraints():
                        print("  SoftConstraint: " + self.pretty_printer.do_print(c, show_exp=True, print_values=True))
                        
                x += 1
                
                
        end = int(round(time.time() * 1000))

    def swizzle_randvars(self, 
                btor     : Boolector, 
                ri       : RandInfo,
                start_rs : int,
                end_rs   : int,
                bound_m  : Dict[FieldModel,VariableBoundModel]):

        # TODO: we must ignore fields that are otherwise being controlled
        if self.debug > 0:
            print("--> swizzle_randvars")

        rand_node_l = []
        rand_e_l = []
        x=start_rs
        swizzled_field = False
        while x < end_rs:
            # For each random variable, select a partition with it's known 
            # domain and add the corresponding constraint
            rs = ri.randsets()[x]
            field_l = rs.rand_fields()
            
            if self.debug > 0:
                print("  " + str(len(field_l)) + " fields in randset")
            
            if rs.rand_order_l is not None:
                # Perform an ordered randomization
                for ro_l in rs.rand_order_l:
                    swizzled_field |= self.swizzle_field_l(ro_l, rs, bound_m, btor)
            else:
                swizzled_field |= self.swizzle_field_l(rs.rand_fields(), rs, bound_m, btor)
                
            x += 1
            
        if not swizzled_field:
            if self.solve_info is not None:
                self.solve_info.n_sat_calls += 1                    
            btor.Sat()
            
        if self.debug > 0:
            print("<-- swizzle_randvars")
            
    def swizzle_field_l(self, field_l, rs, bound_m, btor):
        e = None
        if len(field_l) > 0:
            # Make a copy of the field list so we don't
            # destroy the original
            field_l = field_l.copy()
            
            swizzle_node_l = []
            swizzle_expr_l = []
            max_swizzle = 4

            # Select up to `max_swizzle` fields to swizzle            
            for i in range(max_swizzle):
                if len(field_l) > 0:
                    field_idx = self.randint(0, len(field_l)-1)
                    f = field_l.pop(field_idx)
                    e = self.swizzle_field(f, rs, bound_m)
                    if e is not None:
                        swizzle_expr_l.append(e)
                        swizzle_node_l.append(e.build(btor))
                else:
                    break
                
            while len(swizzle_node_l) > 0:
                # Start by assuming all
                for n in swizzle_node_l:
                    btor.Assume(n)

                if self.solve_info is not None:
                    self.solve_info.n_sat_calls += 1
                if btor.Sat() != btor.SAT:
                    e = swizzle_expr_l.pop()
                    n = swizzle_node_l.pop()
                    if self.debug > 0:
                        print("Randomization constraint failed. Removing last: %s" %
                              self.pretty_printer.print(e))
                else:
                    # Randomization constraints succeeded. Go ahead and assert
                    for n in swizzle_node_l:
                        btor.Assert(n)
                    break
                    
            if self.solve_info is not None:
                self.solve_info.n_sat_calls += 1
            if btor.Sat() != btor.SAT:
                raise Exception("failed to add in randomization (2)")                           
            return True
        else:
            return False
                
            
    def swizzle_field(self, f, rs, bound_m) -> ExprModel:
        ret = None
        
        if self.debug > 0:
            print("Swizzling field %s" % f.name)
             
        if f in rs.dist_field_m.keys():
            if self.debug > 0:
                print("Note: field %s is in dist map" % f.name)
                for d in rs.dist_field_m[f]:
                    print("  Target interval %d" % d.target_range)
            if len(rs.dist_field_m[f]) > 1:
                target_d = self.randint(0, len(rs.dist_field_m[f])-1)
                dist_scope_c = rs.dist_field_m[f][target_d]
            else:
                dist_scope_c = rs.dist_field_m[f][0]
                
            target_w = dist_scope_c.dist_c.weights[dist_scope_c.target_range]
            if target_w.rng_rhs is not None:
                # Dual-bound range
                val_l = target_w.rng_lhs.val()
                val_r = target_w.rng_rhs.val()
                val = self.randint(val_l, val_r)
                if self.debug > 0:
                    print("Select dist-weight range: %d..%d ; specific value %d" % (
                        int(val_l), int(val_r), int(val)))
                ret = ExprBinModel(
                    ExprFieldRefModel(f),
                    BinExprType.Eq,
                    ExprLiteralModel(val, f.is_signed, f.width))
            else:
                # Single value
                val = target_w.rng_lhs.val()
                ret = ExprBinModel(
                    ExprFieldRefModel(f),
                    BinExprType.Eq,
                    ExprLiteralModel(int(val), f.is_signed, f.width))
        else:
            if f in bound_m.keys():
                f_bound = bound_m[f]
                if not f_bound.isEmpty():
                    ret = self.create_rand_domain_constraint(f, f_bound)
                    
        return ret
#                    if e is not None:
#                        n = e.build(btor)
#                        rand_node_l.append(n)
#                        rand_e_l.append(e)
                        
    def create_rand_domain_constraint(self, 
                f : FieldScalarModel, 
                bound_m : VariableBoundModel)->ExprModel:
        e = None
        range_l = bound_m.domain.range_l
        range_idx = self.randint(0, len(range_l)-1)
        range = range_l[range_idx]
        domain = range[1]-range[0]
        
        
        if self.debug > 0:
            print("create_rand_domain_constraint: " + f.name + " range_idx=" + str(range_idx) + " range=" + str(range))
        if domain > 64:
            r_type = self.randint(0, 3)
            r_type = 3 # Note: hard-coded to selecting single value for 
            single_val = self.randint(range[0], range[1])
                
            if r_type >= 0 and r_type <= 2: # range
                # Pretty simple. Partition and randomize
#                bin_sz_h = 1 if int(domain/128) == 0 else int(domain/128)
                bin_sz_h = 1 if int(domain/128) == 0 else int(domain/128)

                if r_type == 0:                
                    # Center value in bin
                    if single_val+bin_sz_h > range[1]:
                        max = range[1]
                        min = range[1]-2*bin_sz_h
                    elif single_val-bin_sz_h < range[0]:
                        max = range[0]+2*bin_sz_h
                        min = range[0]
                    else:
                        max = single_val+bin_sz_h
                        min = single_val-bin_sz_h
                        
                    if self.debug > 0:
                        print("rand_domain range-type is bin center value: center=%d => %d..%d" % (single_val,min,max))
                elif r_type == 1:
                    # Bin starts at value
                    if single_val+2*bin_sz_h > range[1]:
                        max = range[1]
                        min = range[1]-2*bin_sz_h
                    elif single_val-2*bin_sz_h < range[0]:
                        max = range[0]+2*bin_sz_h
                        min = range[0]
                    else:
                        max = single_val+2*bin_sz_h
                        min = single_val
                    if self.debug > 0:
                        print("rand_domain range-type is bin left-target value: left=%d %d..%d" % (single_val, min,max))
                elif r_type == 2:
                    # Bin ends at value
                    if single_val+2*bin_sz_h > range[1]:
                        max = range[1]
                        min = range[1]-2*bin_sz_h
                    elif single_val-2*bin_sz_h < range[0]:
                        max = range[0]+2*bin_sz_h
                        min = range[0]
                    else:
                        max = single_val
                        min = single_val-2*bin_sz_h
                        
                    if self.debug > 0:
                        print("rand_domain range-type is bin right-target value: left=%d %d..%d" % (single_val, min,max))
                 
                e = ExprBinModel(
                    ExprBinModel(
                        ExprFieldRefModel(f),
                        BinExprType.Ge,
                        ExprLiteralModel(
                            min,
                            f.is_signed, 
                            f.width)
                    ),
                    BinExprType.And,
                    ExprBinModel(
                        ExprFieldRefModel(f),
                        BinExprType.Le,
                        ExprLiteralModel(
                            max,
                            f.is_signed, 
                            f.width)
                    )
                )
            elif r_type == 3: # Single value
                if self.debug > 0:
                    print("rand_domain range-type is single value: %d" % single_val)
                e = ExprBinModel(
                        ExprFieldRefModel(f),
                        BinExprType.Eq,
                        ExprLiteralModel(single_val, f.is_signed, f.width))
        else:
            val = self.randint(range[0], range[1])
            if self.debug > 0:
                print("rand_domain on small domain [%d..%d] => %d" % (range[0], range[1], val))
            e = ExprBinModel(
                ExprFieldRefModel(f),
                BinExprType.Eq,
                ExprLiteralModel(val, f.is_signed, f.width))

        return e
    
    def randint(self, low, high):
        return self.randstate.randint(low, high)
#        if low > high:
#            tmp = low
#            low = high
#            high = tmp
#
#        return random.randint(low,high)

    def randbits(self, nbits):
#        if Randomizer._rng is None:
#            Randomizer._rng = random.Random(random.randrange(sys.maxsize))
#        return Randomizer._rng.randint(0, (1<<nbits)-1)
        return random.randint(0, (1<<nbits)-1)

    @staticmethod            
    def _next():
#        if Randomizer._rng is None:
#            Randomizer._rng = random.Random(random.randrange(sys.maxsize))
#        ret = Randomizer._rng.randint(0, 0xFFFFFFFF)
        ret = random.randint(0, 0xFFFFFFFF)
#         ret = (Randomizer._state_p[0] + Randomizer._state_p[1]) & 0xFFFFFFFF
#         Randomizer._state_p[1] ^= Randomizer._state_p[0]
#         Randomizer._state_p[0] = (((Randomizer._state_p[0] << 55) | (Randomizer._state_p[0] >> 9))
#             ^ Randomizer._state_p[1] ^ (Randomizer._state_p[1] << 14))
#         Randomizer._state_p[1] = (Randomizer._state_p[1] << 36) | (Randomizer._state_p[1] >> 28)
        
        return ret

    def create_diagnostics_1(self, active_randsets) -> str:
        ret = ""
        
        btor = Boolector()
        btor.Set_opt(pyboolector.BTOR_OPT_INCREMENTAL, True)
        btor.Set_opt(pyboolector.BTOR_OPT_MODEL_GEN, True)
        model_valid = False
        
        diagnostic_constraint_l = [] 
        diagnostic_field_l = []
        
        # First, determine how many randsets are actually failing
        i = 0
        while i < len(active_randsets):
            rs = active_randsets[i]
            for f in rs.all_fields():
                f.build(btor)

            # Assume that we can omit all soft constraints, since they
            # will have already been omitted (?)                
            constraint_l = list(map(lambda c:(c,c.build(btor)), filter(lambda c:not isinstance(c,ConstraintSoftModel), rs.constraints())))
                
            for c in constraint_l:
                btor.Assume(c[1])

            if btor.Sat() != btor.SAT:
                # Save fields and constraints if the randset doesn't 
                # solve on its own
                diagnostic_constraint_l.extend(constraint_l)
                diagnostic_field_l.extend(rs.fields())
                
            i += 1
            

        problem_constraints = []
        solving_constraints = []
        # Okay, now perform a series of solves to identify
        # constraints that are actually a problem
        for c in diagnostic_constraint_l:
            btor.Assume(c[1])
            model_valid = False
            
            if btor.Sat() != btor.SAT:
                # This is a problematic constraint
                # Save it for later
                problem_constraints.append(c[0])
            else:
                # Not a problem. Assert it now
                btor.Assert(c[1])
                solving_constraints.append(c[0])
                model_valid = True
#                problem_constraints.append(c[0])
                
        if btor.Sat() != btor.SAT:
            raise Exception("internal error: system should solve")
        
        # Okay, we now have a constraint system that solves, and
        # a list of constraints that are a problem. We want to 
        # resolve the value of all variables referenced by the 
        # solving constraints so and then display the non-solving
        # constraints. This will (hopefully) help highlight the
        # reason for the failure
        for c in solving_constraints:
            c.accept(RefFieldsPostRandVisitor())

        ret += "Problem Constraints:\n"
        for i,pc in enumerate(problem_constraints):

            ret += "Constraint %d: %s\n" % (i, SourceInfo.toString(pc.srcinfo))
            ret += ModelPrettyPrinter.print(pc, print_values=True)
            ret += ModelPrettyPrinter.print(pc, print_values=False)

        for rs in active_randsets:
            for f in rs.all_fields():
                f.dispose()
            
        return ret

    def create_diagnostics(self, active_randsets) -> str:
        
        btor = Boolector()
        btor.Set_opt(pyboolector.BTOR_OPT_INCREMENTAL, True)
        btor.Set_opt(pyboolector.BTOR_OPT_MODEL_GEN, True)
        model_valid = False
        
        diagnostic_constraint_l = [] 
        diagnostic_field_l = []
        
        # First, determine how many randsets are actually failing
        i = 0
        while i < len(active_randsets):
            rs = active_randsets[i]
            for f in rs.all_fields():
                f.build(btor)

            # Assume that we can omit all soft constraints, since they
            # will have already been omitted (?)                
            constraint_l = list(map(lambda c:(c,c.build(btor)), filter(lambda c:not isinstance(c,ConstraintSoftModel), rs.constraints())))
                
            for c in constraint_l:
                btor.Assume(c[1])

            if btor.Sat() != btor.SAT:
                # Save fields and constraints if the randset doesn't 
                # solve on its own
                diagnostic_constraint_l.extend(constraint_l)
                diagnostic_field_l.extend(rs.fields())
                
            i += 1
            
        problem_sets = []
        degree = 1
        
        while True:
            init_size = len(diagnostic_constraint_l)
            tmp_l = []

            ret = self._collect_failing_constraints(
                btor, 
                diagnostic_constraint_l,
                0, 
                degree,
                tmp_l,
                problem_sets)
                
            if len(diagnostic_constraint_l) == init_size and degree > 3:
                break
            else:
                degree += 1

        if Randomizer.EN_DEBUG > 0:
            print("%d constraints remaining ; %d problem sets" % (len(diagnostic_constraint_l), len(problem_sets)))

        # Assert the remaining constraints
        for c in diagnostic_constraint_l:
            btor.Assert(c[1])
                
        if btor.Sat() != btor.SAT:
            raise Exception("internal error: system should solve")
        
        # Okay, we now have a constraint system that solves, and
        # a list of constraints that are a problem. We want to 
        # resolve the value of all variables referenced by the 
        # solving constraints so and then display the non-solving
        # constraints. This will (hopefully) help highlight the
        # reason for the failure
        
        ret = ""
        for ps in problem_sets:
            ret += ("Problem Set: %d constraints\n" % len(ps))
            for pc in ps:
                ret += "  %s:\n" % SourceInfo.toString(pc[0].srcinfo)
                ret += "    %s" % ModelPrettyPrinter.print(pc[0], print_values=False)

            pc = []
            for c in ps:
                pc.append(c[0])
            
            lint_r = LintVisitor().lint(
              [],
              pc)
            
            if lint_r != "":
                ret += "Lint Results:\n" + lint_r
                
        for rs in active_randsets:
            for f in rs.all_fields():
                f.dispose()
            
        return ret            
    
    def _collect_failing_constraints(self,
                                     btor,
                                     src_constraint_l,
                                     idx,
                                     max,
                                     tmp_l,
                                     fail_set_l):
        ret = False
        if len(tmp_l) < max:
            i = idx
            while i < len(src_constraint_l):
                tmp_l.append(i)
                ret = self._collect_failing_constraints(
                    btor, src_constraint_l, i+1, max, tmp_l, fail_set_l)
                tmp_l.pop()
                if ret:
                    src_constraint_l.pop(i)
                else:
                    i += 1
        else:
            # Assume full set of collected constraints
            if Randomizer.EN_DEBUG:
                print("Assume: " + str(tmp_l))
            for c in tmp_l:
                btor.Assume(src_constraint_l[c][1])
            if btor.Sat() != btor.SAT:
                # Set failed. Add to fail_set
                fail_s = []
                for ci in tmp_l:
                    fail_s.append(src_constraint_l[ci])
                fail_set_l.append(tuple(fail_s))
                ret = True
                
        return ret

    
    @staticmethod
    def do_randomize(
            randstate,
            srcinfo : SourceInfo,
            field_model_l : List[FieldModel],
            constraint_l : List[ConstraintModel] = None,
            debug=0,
            lint=0,
            solve_fail_debug=0):
        if profile_on():
            solve_info = SolveInfo()
            solve_info.totaltime = time.time()
            randomize_start(srcinfo, field_model_l, constraint_l)
        else:
            solve_info = None
        
        # All fields passed to do_randomize are treated
        # as randomizable
#        if Randomizer._rng is None:
#            Randomizer._rng = random.Random(random.randrange(sys.maxsize))
#        seed = Randomizer._rng.randint(0, (1 << 64)-1)
            
        seed = random.randint(0, (1<<64)-1)
        
        clear_soft_priority = ClearSoftPriorityVisitor()
        
        for f in field_model_l:
            f.set_used_rand(True, 0)
            clear_soft_priority.clear(f)
           
        if debug > 0: 
            print("Initial Model:")        
            for fm in field_model_l:
                print("  " + ModelPrettyPrinter.print(fm))
                
        # First, invoke pre_randomize on all elements
        for fm in field_model_l:
            fm.pre_randomize()
            
        if constraint_l is None:
            constraint_l = []
            
        for c in constraint_l:
            clear_soft_priority.clear(c)

        # Collect all variables (pre-array) and establish bounds            
        bounds_v = VariableBoundVisitor()
        bounds_v.process(field_model_l, constraint_l, False)

        # TODO: need to handle inline constraints that impact arrays
        constraints_len = len(constraint_l)
        for fm in field_model_l:
            constraint_l.extend(ArrayConstraintBuilder.build(
                fm, bounds_v.bound_m))
            # Now, handle dist constraints
            DistConstraintBuilder.build(seed, fm)
            
        for c in constraint_l:
            constraint_l.extend(ArrayConstraintBuilder.build(
                c, bounds_v.bound_m))
            # Now, handle dist constraints
            DistConstraintBuilder.build(seed, c)

        # If we made changes during array remodeling,
        # re-run bounds checking on the updated model
#        if len(constraint_l) != constraints_len:
        bounds_v.process(field_model_l, constraint_l)

        if debug > 0:
            print("Final Model:")        
            for fm in field_model_l:
                print("  " + ModelPrettyPrinter.print(fm))
            for c in constraint_l:
                print("  " + ModelPrettyPrinter.print(c, show_exp=True))

#        if lint > 0:
#            LintVisitor().lint(
#                field_model_l,
#                constraint_l)
            

        r = Randomizer(
            randstate,
            solve_info=solve_info,
            debug=debug, 
            lint=lint, 
            solve_fail_debug=solve_fail_debug)
#        if Randomizer._rng is None:
#            Randomizer._rng = random.Random(random.randrange(sys.maxsize))
        ri = RandInfoBuilder.build(field_model_l, constraint_l, Randomizer._rng)
        
        try:
            r.randomize(ri, bounds_v.bound_m)
        finally:
            # Rollback any constraints we've replaced for arrays
            if solve_info is not None:
                solve_info.totaltime = int((time.time() - solve_info.totaltime)*1000)
                randomize_done(srcinfo, solve_info)
            for fm in field_model_l:
                ConstraintOverrideRollbackVisitor.rollback(fm)
        
        for fm in field_model_l:
            fm.post_randomize()
        
        
        # Process constraints to identify variable/constraint sets
        
