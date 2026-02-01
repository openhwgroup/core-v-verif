'''
Created on Jun 26, 2021

@author: mballance
'''
from vsc.model.model_visitor import ModelVisitor
from vsc.model.expr_model import ExprModel
from vsc.model.expr_literal_model import ExprLiteralModel
from vsc.visitors.expr2field_visitor import Expr2FieldVisitor
from vsc.model.expr_fieldref_model import ExprFieldRefModel
from vsc.model.expr_indexed_field_ref_model import ExprIndexedFieldRefModel
from vsc.model.value_scalar import ValueScalar

class ForeachRefExpander(ModelVisitor):
    """Expand index-variable references in a foreach constraint"""
    
    EN_DEBUG = 0
    
    def __init__(self, index_set):
        self.index_set = index_set
        self.expr2field = Expr2FieldVisitor()
        self._expr = None
        self._field = None
        self._refs_index_var = False
        
    def expand(self, e : ExprModel) -> ExprModel:
        if ForeachRefExpander.EN_DEBUG > 0:
            print("--> ForeachRefExpander::expand")
        self._field = None
        self._expr = None
        
        # Tracks whether a foreach index is used anywhere in the expression
        self._refs_index_var = False
        
        e.accept(self) 
        
        if self._refs_index_var:
            if self._expr is not None:
                ret = self._expr
            elif self._field is not None:
                ret = ExprFieldRefModel(self._field)
            else:
                raise Exception("references index vars, but failed to resolve field")
        else:
            ret = None
        
        if ForeachRefExpander.EN_DEBUG > 0:
            print("<-- ForeachRefExpander::expand ret=%s" % str(ret))
            
        return ret
    
    def visit_expr_fieldref(self, e):
        if ForeachRefExpander.EN_DEBUG > 0:
            print("--> ForeachRefExpander::visit_expr_fieldref %s" % e.fm.fullname)

        # Save a reference to the field
        self._field = e.fm
        
        # If the target is one of the index variables, then 
        # note that and grab the actual value for use
        if e.fm in self.index_set:
            if ForeachRefExpander.EN_DEBUG > 0:
                print("ForeachRefExpander: field is an index. Replacing with %d" % (
                    int(e.fm.get_val()),))
            self._refs_index_var = True
            self._expr = ExprLiteralModel(int(e.fm.get_val()), True, 32)
            
        if ForeachRefExpander.EN_DEBUG > 0:
            print("<-- ForeachRefExpander::visit_expr_fieldref")
            
    def visit_expr_indexed_fieldref(self, e : ExprIndexedFieldRefModel):
        if ForeachRefExpander.EN_DEBUG > 0:
            print("--> ForeachRefExpander::visit_indexed_fieldref")
            
        # See if the base involves an index
        e.root.accept(self)
        
        if self._field is not None:
            # Resolve relative to the target
            self._field = e.get_target(self._field)

        # Propagate the _field up, but not the _expr            
        self._expr = None
        
        if ForeachRefExpander.EN_DEBUG > 0:
            print("<-- ForeachRefExpander::visit_indexed_fieldref %s" % str(self._field))
    
    def visit_expr_array_subscript(self, s):
        if ForeachRefExpander.EN_DEBUG > 0:
            print("--> ForeachRefExpander::visit_expr_array_subscript")
            
        # First, resolve the root
        s.lhs.accept(self)
        
        if self._field is not None:
            # Yes, we are able to follow the trail
            base = self._field

            # Check to see whether this includes an index reference
            s.rhs.accept(self)
            
            self._field = base.field_l[int(s.rhs.val())]
            
        # Propagate the _field up, but not the _expr
        self._expr = None
            
        if ForeachRefExpander.EN_DEBUG > 0:
            print("<-- ForeachRefExpander::visit_expr_array_subscript field=%s" % str(self._field))
        