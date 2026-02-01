

# Created on Apr 4, 2020
#
# @author: ballance

from typing import Dict, List

from vsc.model.bin_expr_type import BinExprType
from vsc.model.constraint_foreach_model import ConstraintForeachModel
from vsc.model.constraint_if_else_model import ConstraintIfElseModel
from vsc.model.constraint_implies_model import ConstraintImpliesModel
from vsc.model.constraint_inline_scope_model import ConstraintInlineScopeModel
from vsc.model.constraint_soft_model import ConstraintSoftModel
from vsc.model.constraint_unique_model import ConstraintUniqueModel
from vsc.model.enum_field_model import EnumFieldModel
from vsc.model.expr_array_subscript_model import ExprArraySubscriptModel
from vsc.model.expr_bin_model import ExprBinModel
from vsc.model.expr_fieldref_model import ExprFieldRefModel
from vsc.model.expr_in_model import ExprInModel
from vsc.model.expr_literal_model import ExprLiteralModel
from vsc.model.field_array_model import FieldArrayModel
from vsc.model.field_model import FieldModel
from vsc.model.field_scalar_model import FieldScalarModel
from vsc.model.model_visitor import ModelVisitor
from vsc.model.variable_bound_bounds_max_propagator import VariableBoundBoundsMaxPropagator
from vsc.model.variable_bound_bounds_min_propagator import VariableBoundBoundsMinPropagator
from vsc.model.variable_bound_enum_model import VariableBoundEnumModel
from vsc.model.variable_bound_eq_propagator import VariableBoundEqPropagator
from vsc.model.variable_bound_expr_max_propagator import VariableBoundExprMaxPropagator
from vsc.model.variable_bound_expr_min_propagator import VariableBoundExprMinPropagator
from vsc.model.variable_bound_in_propagator import VariableBoundInPropagator
from vsc.model.variable_bound_max_propagator import VariableBoundMaxPropagator
from vsc.model.variable_bound_min_propagator import VariableBoundMinPropagator
from vsc.model.variable_bound_model import VariableBoundModel
from vsc.model.variable_bound_scalar_model import VariableBoundScalarModel
from vsc.model.variable_bound_vareq_propagator import VariableBoundVarEqPropagator
from vsc.visitors.is_const_expr_visitor import IsConstExprVisitor
from vsc.visitors.is_nonrand_expr_visitor import IsNonRandExprVisitor
from vsc.visitors.model_pretty_printer import ModelPrettyPrinter
from vsc.visitors.expr2field_visitor import Expr2FieldVisitor


class VariableBoundVisitor(ModelVisitor):
    """Establishes bounds for each variable based on constraints"""
    
    def __init__(self):
        super().__init__()
        self.field_info_m : Dict[FieldModel, VariableBoundVisitor.VarInfo] = {}
        # Collect variables during phase1
        # Compute bounds during phase2
        self.phase = 0
        self.bound_m : Dict[FieldModel, VariableBoundModel] = {}
        self._propagator = None
        self._expr = None
        self.depth = 0
        self.process_subscript = True
        self.propagators = []
        
        # Result data from processing expressions
        self.field = None
        self.const = None
        
    def process(self, 
                variables,
                constraints,
                process_subscript=True) -> Dict[FieldModel, 'VarInfo']:
        self.bound_m : Dict[FieldModel, 'VarInfo'] = {}
        self.process_subscript = process_subscript
        
        # Tracks how deep we are in expressions, so we know
        # how to process expressions
        self.depth = 0
        
        self.phase = 0
        for v in variables:
            v.accept(self)
        for c in constraints:
            c.accept(self)
            
        self.phase = 1
        for v in variables:
            v.accept(self)
        for c in constraints:
            c.accept(self)
            
        # Now, process propagators until we stabilize
        changed = True
        count = 0
        limit = 100
        while changed and count < limit:
            changed = False
            for p in self.propagators:
                changed |= p.propagate()
            count += 1
            
        if count >= limit:
            print("Note: variable bounds model failed to converge in " + str(limit) + " iterations")
            
        # Update data calcuated from domain ranges
        for f,b in self.bound_m.items():
            b.update()
#            print(b.toString())
            
        

    def visit_constraint_if_else(self, c:ConstraintIfElseModel):
        self.depth += 1
        super().visit_constraint_if_else(c)
        self.depth -= 1
    
    def visit_constraint_implies(self, c:ConstraintImpliesModel):
        self.depth += 1
        super().visit_constraint_implies(c)
        self.depth -= 1
            
    def visit_constraint_inline_scope(self, c:ConstraintInlineScopeModel):
        for cc in c.constraint_l:
            cc.accept(self)
    
    def visit_constraint_foreach(self, f:ConstraintForeachModel):
        # Don't go into an unexpanded foreach block. This 
        # construct is a meta-constraint that will be expanded
        pass
    
    def visit_constraint_soft(self, c : ConstraintSoftModel):
        # Ignore soft constraints, since they may be at odds with reality
        pass
    
    def visit_constraint_unique(self, c:ConstraintUniqueModel):
        # Don't go into an unexpanded unique block. This 
        # construct is a meta-constraint that will be expanded
        pass
    
    def visit_expr_bin(self, e:ExprBinModel):
        # TODO: We'll need to deal with expressions that involve variables
        # An alias is the simplest relationship. A == B means that there is
        # a single bound for both variables, and all relationships on A and B
        # contribute to this single bound

        # Don't attempt to deal with subscripts when we're
        # establishing array domains.        
        if self.phase == 0 or self.depth > 0:
            super().visit_expr_bin(e)
        else: # phase==1

            if not self.process_subscript and (
                isinstance(e.lhs, ExprArraySubscriptModel) or 
                isinstance(e.rhs, ExprArraySubscriptModel)):
                return
            
            lhs_fm = Expr2FieldVisitor().field(e.lhs, fail_on_failure=False)
            rhs_fm = Expr2FieldVisitor().field(e.rhs, fail_on_failure=False)

            # Check whether the expressions involve *any* random variables            
            lhs_is_nonrand = IsNonRandExprVisitor().is_nonrand(e.lhs)
            rhs_is_nonrand = IsNonRandExprVisitor().is_nonrand(e.rhs)

            if lhs_fm is not None and lhs_fm in self.bound_m.keys():                
                lhs_bounds = self.bound_m[lhs_fm]
            else:
                lhs_bounds = None
                
            if rhs_fm is not None and rhs_fm in self.bound_m.keys():                
                rhs_bounds = self.bound_m[rhs_fm]
            else:
                rhs_bounds = None
                
            propagator = None
                
            if lhs_bounds is not None and rhs_bounds is not None:
                # Two-sided relationship involving fields
                propagator = self.lhsvar_rhsvar_propagator(
                    lhs_bounds, 
                    e.op, 
                    rhs_bounds)
                pass
            elif lhs_bounds is not None:
                # left-hand field and no right-hand field
                if rhs_is_nonrand:
                    propagator = self.lhsvar_rhsnre_propagator(
                        lhs_bounds, 
                        e.op, 
                        e.rhs)
            elif rhs_fm is not None:
                # right-hand field and no left-hand field
                if lhs_is_nonrand:
                    propagator = self.lhsnre_rhsvar_propagator(
                        e.lhs, 
                        e.op, 
                        rhs_bounds)

            if propagator is not None:
                self.propagators.append(propagator)
                
    def lhsvar_rhsvar_propagator(self,
                    lhs_bounds,
                    op,
                    rhs_bounds):
        propagator = None

        if op == BinExprType.Lt:
            # <v1> < <v2> <-> <v1.max> <= <v2.max-1>
            propagator = VariableBoundBoundsMaxPropagator(
                lhs_bounds, rhs_bounds, -1)
        elif op == BinExprType.Le:
            # <v1> <= <v2> <-> <v1.max> <= <v2.max>
            propagator = VariableBoundBoundsMaxPropagator(
                lhs_bounds, rhs_bounds)
        elif op == BinExprType.Gt:
            # <v1> > <v2> <-> <
            propagator = VariableBoundBoundsMinPropagator(
                lhs_bounds, rhs_bounds, 1)
        elif op == BinExprType.Ge:
            propagator = VariableBoundBoundsMinPropagator(
                lhs_bounds, rhs_bounds)
        elif op == BinExprType.Eq:
            propagator = VariableBoundVarEqPropagator(
                lhs_bounds,
                rhs_bounds)
            
        if propagator is not None:
            lhs_bounds.add_propagator(propagator)

        return propagator
    
    def lhsvar_rhsnre_propagator(self,
                    lhs_bounds,
                    op,
                    rhs_e):
        propagator = None
        if op == BinExprType.Lt:
            # The max bound is 
            propagator = VariableBoundExprMaxPropagator(
                lhs_bounds,
                ExprBinModel(
                    rhs_e,
                    BinExprType.Sub,
                    ExprLiteralModel(1, False, 4)))
        elif op == BinExprType.Le:
            # The max bound is 
            propagator = VariableBoundExprMaxPropagator(
                lhs_bounds,
                rhs_e)
        elif op == BinExprType.Gt:
            # The minimum bound is 1+RHS
            propagator = VariableBoundExprMinPropagator(
                lhs_bounds,
                ExprBinModel(
                    rhs_e,
                    BinExprType.Add,
                        ExprLiteralModel(1, False, 4)))
        elif op == BinExprType.Ge:
            # The minimum bound is 1+ RHS
            propagator = VariableBoundExprMinPropagator(
                lhs_bounds,
                rhs_e)
        elif op == BinExprType.Eq:
            # Know that the right-hand side is a non-rand quantity
            # This pins the left-hand variable to a single value
            propagator = VariableBoundEqPropagator(
                lhs_bounds,
                rhs_e,
                True)

        if propagator is not None:
            lhs_bounds.add_propagator(propagator)
            
        return propagator
    
    def lhsnre_rhsvar_propagator(self,
                    lhs_e,
                    op,
                    rhs_bounds):
        propagator = None
        if op == BinExprType.Lt:
            # <expr> < <var>  <-> <var> >= <expr>+1
            # Sets the minimum bound for the variable
            propagator = VariableBoundExprMinPropagator(
                rhs_bounds,
                ExprBinModel(
                    lhs_e,
                    BinExprType.Add,
                    ExprLiteralModel(1, False, 4)))
        elif op == BinExprType.Le:
            # <expr> <= <var> <-> <var> >= <expr>
            propagator = VariableBoundExprMinPropagator(
                rhs_bounds,
                lhs_e)
        elif op == BinExprType.Gt:
            # <expr> > <var> <-> <var> <= <expr>-1
            propagator = VariableBoundExprMaxPropagator(
                rhs_bounds,
                ExprBinModel(
                    lhs_e,
                    BinExprType.Sub,
                        ExprLiteralModel(1, False, 4)))
        elif op == BinExprType.Ge:
            # <expr> >= <var> <-> <var> <= <expr>
            propagator = VariableBoundExprMaxPropagator(
                rhs_bounds,
                lhs_e)
        elif op == BinExprType.Eq:
            propagator = VariableBoundEqPropagator(
                rhs_bounds,
                lhs_e,
                True)

        if propagator is not None:
            rhs_bounds.add_propagator(propagator)        
        return propagator

    def visit_expr_in(self, e : ExprInModel):
        if self.phase == 1:
            if self.depth > 0:
                pass
            else:
                lhs_fm = Expr2FieldVisitor().field(e.lhs, fail_on_failure=False)

            # Check whether the expressions involve *any* random variables            
#            lhs_is_nonrand = IsNonRandExprVisitor().is_nonrand(e.lhs)
#            rhs_is_nonrand = IsNonRandExprVisitor().is_nonrand(e.rhs)
                    
                if lhs_fm is not None and lhs_fm in self.bound_m.keys():
                    lhs_bounds = self.bound_m[lhs_fm]
                else:
                    lhs_bounds = None
                    
                if lhs_bounds is not None:
                    is_nre_v = IsNonRandExprVisitor()

                    # Confirm that all expressions are non-random
                    is_nre = True
                    for r in e.rhs.rl:
                        if isinstance(r, list):
                            is_nre &= is_nre_v.is_nonrand(r[0])
                            is_nre &= is_nre_v.is_nonrand(r[1])
                        elif isinstance(r, ExprFieldRefModel):
                            # For now. This is likely a reference
                            # to an array
                            is_nre = False
                        else:
                            is_nre &= is_nre_v.is_nonrand(r)
                    
                        if not is_nre:
                            break

                    if is_nre:
                        propagator = VariableBoundInPropagator(lhs_bounds, e.rhs)
                        lhs_bounds.add_propagator(propagator)
                        propagator.propagate()
                    
    def visit_expr_array_subscript(self, s):
        # This only exists until we flatten out array references
        pass
                
    def visit_expr_fieldref(self, e):
        if self.phase == 0:
            # Collect fields that may just be referenced
            e.fm.accept(self)
        elif self.phase == 1:
            # TODO: We're collecting fields that are part of 
            # a limiting expression. Need to add the propagator
            # to these variables as well
            if e.fm in self.bound_m.keys():
                bounds = self.bound_m[e.fm]
                bounds.constrained = True
#                bounds.add_propagator(self._propagator)
            else:
                raise Exception("Field " + e.fm.fullname + " not in map")
            
    def visit_scalar_field(self, f:FieldScalarModel):
        if self.phase == 0:
            # Fill in basic bound info
            if not f in self.bound_m.keys():
                bounds = VariableBoundScalarModel(f)
                self.bound_m[f] = bounds
                
    def visit_enum_field(self, f:EnumFieldModel):
        if self.phase == 0:
            if not f in self.bound_m.keys():
                bounds = VariableBoundEnumModel(f)
                self.bound_m[f] = bounds
                
                
