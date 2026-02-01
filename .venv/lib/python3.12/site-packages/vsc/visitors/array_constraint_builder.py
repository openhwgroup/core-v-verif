'''
Created on May 18, 2020

@author: ballance
'''

from typing import Dict, Set
import typing

from vsc.model.constraint_block_model import ConstraintBlockModel
from vsc.model.constraint_foreach_model import ConstraintForeachModel
from vsc.model.constraint_scope_model import ConstraintScopeModel
from vsc.model.expr_fieldref_model import ExprFieldRefModel
from vsc.model.expr_literal_model import ExprLiteralModel
from vsc.model.expr_model import ExprModel
from vsc.model.field_model import FieldModel
from vsc.model.field_array_model import FieldArrayModel
from vsc.model.model_visitor import ModelVisitor
from vsc.model.variable_bound_model import VariableBoundModel
from vsc.visitors.constraint_copy_builder import ConstraintCopyBuilder, \
    ConstraintCollector
from vsc.visitors.constraint_override_visitor import ConstraintOverrideVisitor
from vsc.model.constraint_inline_scope_model import ConstraintInlineScopeModel
from vsc.model.expr_array_subscript_model import ExprArraySubscriptModel
from vsc.visitors.model_pretty_printer import ModelPrettyPrinter
from vsc.visitors.has_indexvar_visitor import HasIndexVarVisitor
from vsc.visitors.foreach_ref_expander import ForeachRefExpander
from vsc.visitors.expr2field_visitor import Expr2FieldVisitor


class ArrayConstraintBuilder(ConstraintOverrideVisitor):
    
    def __init__(self, bound_m : Dict[FieldModel,VariableBoundModel]):
        super().__init__()
        self.index_set : Set[FieldModel] = set()
        self.bound_m = bound_m
        self.phase = 0
        self.foreach_scope_s = []
        self.constraint_collector_s = []
        self.foreach_ref_expander = ForeachRefExpander(self.index_set)
        
    @staticmethod
    def build(m, bound_m : typing.Dict[FieldModel,VariableBoundModel]):
        from ..visitors.model_pretty_printer import ModelPrettyPrinter
        builder = ArrayConstraintBuilder(bound_m)
        builder.phase = 0
        m.accept(builder)
        builder.phase = 1
        m.accept(builder)
        
#        print("--> ArrayConstraintBuilder")
#        print("Model: " + ModelPrettyPrinter.print(m))
#        print("<-- ArrayConstraintBuilder")
        
        return builder.constraints
    
    def visit_constraint_foreach(self, f:ConstraintForeachModel):
        # Instead of just performing a straight copy, expand
        # the constraints
        if self.phase != 1:
            return 
        
        scope = ConstraintInlineScopeModel()
        if len(self.foreach_scope_s) == 0:
            # override expects us to be in a scope already
            self.override_constraint(scope)
        self.foreach_scope_s.append(scope)
        
        self.index_set.add(f.index)
        with ConstraintCollector(self, scope) as cc:
            # TODO: need to be a bit more flexible in getting the size
            # Ensure the array is big enough
            
            fm = Expr2FieldVisitor().field(f.lhs, True)

            for i in range(len(fm.field_l)):
                f.index.set_val(i)
                for c in f.constraint_l:
                    c.accept(self)

        if len(self.foreach_scope_s) > 1:
            for c in scope.constraint_l:
                self.foreach_scope_s[-2].constraint_l.append(c)

        self.index_set.remove(f.index)
        self.foreach_scope_s.pop()

    def visit_expr_array_sum(self, s):
        # Don't recurse into this
        pass

    def visit_expr_array_subscript(self, s : ExprArraySubscriptModel):
        if self.phase != 1:
            return

        e = self.foreach_ref_expander.expand(s)

        if e is not None:
            self._expr = e
        else:
            ConstraintCopyBuilder.visit_expr_array_subscript(self, s)
                            
#         if isinstance(s.rhs, ExprFieldRefModel) and s.rhs.fm in self.index_set:
#             # Convert this index into a direct reference
#             self._expr = ExprFieldRefModel(
#                 s.lhs.fm.field_l[int(s.rhs.fm.get_val())])
#         else:
#             ConstraintCopyBuilder.visit_expr_array_subscript(self, s)
        
    def visit_expr_fieldref(self, e : ExprFieldRefModel):
        if self.phase != 1:
            return

        e_p = self.foreach_ref_expander.expand(e)
        
        if e_p is not None:
            self._expr = e_p
        else:
            ConstraintCopyBuilder.visit_expr_fieldref(self, e)
            
        
#         print("visit_expr_fieldref: in_index=%d" % (e.fm in self.index_set))
#         if e.fm in self.index_set:
#             # Replace the index with the appropriate literal value
#             self._expr = ExprLiteralModel(int(e.fm.get_val()), False, 32)
#         else:
#             ConstraintCopyBuilder.visit_expr_fieldref(self, e)
            
    def visit_expr_indexed_fieldref(self, e):
        
        e_p = self.foreach_ref_expander.expand(e)
        
        if e_p is not None:
            self._expr = e_p
        else:
            ConstraintCopyBuilder.visit_expr_indexed_fieldref(self, e)
            
#         print("visit_expr_indexed_fieldref: e.root type=%s" % (str(type(e.root))))
#         if isinstance(e.root, ExprArraySubscriptModel) and HasIndexVarVisitor(self.index_set).has(e.root.rhs):
#             print("  expansion")
#             actual_root = e.root.lhs.fm.field_l[int(e.root.rhs.fm.get_val())]
#             self._expr = ExprFieldRefModel(e.get_target(actual_root))
#         else:
#             ConstraintCopyBuilder.visit_expr_indexed_fieldref(self, e)
            
    def visit_field_scalar_array(self, f:FieldArrayModel):
        if self.phase == 0:
            # TODO: this logic is for rand-sized array fields
            if f.is_rand_sz:
                size_bound = self.bound_m[f.size]
                range_l = size_bound.domain.range_l
                max_size = int(range_l[-1][1])

                # TODO: how do we manage a max size here?                
                if max_size > 100000:
                    raise Exception("Max size for array " + f.name + " (" + str(max_size) + " exceeds 100000")
                
                if len(f.field_l) < max_size:
                    # Extend the size appropriately
                    for i in range(max_size-len(f.field_l)):
                        f.add_field()
        elif self.phase == 1:
            if not f.is_scalar:
                # Need to recurse into sub-fields for non-scalar arrays
                for sf in f.field_l:
                    sf.accept(self)

        