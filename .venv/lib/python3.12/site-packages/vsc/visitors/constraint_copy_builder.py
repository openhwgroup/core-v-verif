'''
Created on May 18, 2020

@author: ballance
'''
from vsc.model.constraint_block_model import ConstraintBlockModel
from vsc.model.constraint_dist_model import ConstraintDistModel
from vsc.model.constraint_expr_model import ConstraintExprModel
from vsc.model.constraint_foreach_model import ConstraintForeachModel
from vsc.model.constraint_if_else_model import ConstraintIfElseModel
from vsc.model.constraint_implies_model import ConstraintImpliesModel
from vsc.model.constraint_inline_scope_model import ConstraintInlineScopeModel
from vsc.model.constraint_model import ConstraintModel
from vsc.model.constraint_scope_model import ConstraintScopeModel
from vsc.model.constraint_soft_model import ConstraintSoftModel
from vsc.model.constraint_unique_model import ConstraintUniqueModel
from vsc.model.dist_weight_expr_model import DistWeightExprModel
from vsc.model.expr_array_subscript_model import ExprArraySubscriptModel
from vsc.model.expr_bin_model import ExprBinModel
from vsc.model.expr_cond_model import ExprCondModel
from vsc.model.expr_in_model import ExprInModel
from vsc.model.expr_range_model import ExprRangeModel
from vsc.model.expr_rangelist_model import ExprRangelistModel
from vsc.model.expr_unary_model import ExprUnaryModel
from vsc.model.model_visitor import ModelVisitor
from vsc.visitors.model_pretty_printer import ModelPrettyPrinter


class ConstraintCollector(object):
    """Creates a copy of a given constraints"""
    
    def __init__(self, builder, scope):
        self._builder = builder
        self._scope = scope
        self._constraints = None
        self._expr = None
        
    @property
    def constraints(self):
        return self._constraints
    
    def __enter__(self):
        self._constraints = self._builder.constraints
        self._builder.constraints = []
        self._builder.do_copy_level += 1
        self._builder.collector_s.append(self)
        return self
        
    def __exit__(self, t, v, tb):
        for c in self._builder.constraints:
            self._scope.constraint_l.append(c)
        self._builder.constraints = self._constraints
        self._builder.do_copy_level -= 1
        self._builder.collector_s.pop()


class ConstraintCopyBuilder(ModelVisitor):
    
    def __init__(self):
        super().__init__()
        self.constraints : List[ConstraintBlockModel] = []
        self.constraints_s : List[List[ConstraintModel]] = []
        self.collector_s = []
        self.do_copy_level = 0
        
    @staticmethod
    def copy(m):
        copier = ConstraintCopyBuilder()
        copier.do_copy_level += 1
        m.accept(copier)
        copier.do_copy_level -= 1
        return copier.constraints
        
    def visit_constraint_block(self, c:ConstraintBlockModel):
        if self.do_copy_level > 0:
            ret = ConstraintBlockModel(c.name)
            ret.enabled = c.enabled
            ret.is_dynamic = c.is_dynamic

            with ConstraintCollector(self, ret):
                for cs in c.constraint_l:
                    cs.accept(self)
            self.constraints.append(ret)
        else:
            super().visit_constraint_block(c)
            
    def visit_constraint_dist(self, c):
        if self.do_copy_level > 0:
            weights = []
            for w in c.weights:
                weights.append(self.expr(w))
                
            ret = ConstraintDistModel(
                self.expr(c.lhs),
                weights)
            
            self.constraints.append(ret)
        else:
            super().visit_constraint_dist(c)
            
    def visit_dist_weight(self, w):
        if self.do_copy_level > 0:
            self._expr = DistWeightExprModel(
                self.expr(w.rng_lhs),
                None if w.rng_rhs is None else self.expr(w.rng_rhs),
                self.expr(w.weight))
        else:
            super().visit_dist_weight(w)
        
    def visit_constraint_expr(self, c:ConstraintExprModel):
        if self.do_copy_level > 0:
            ret = ConstraintExprModel(self.expr(c.e))
            self.constraints.append(ret)
        else:
            super().visit_constraint_expr(c)
        
    def visit_constraint_foreach(self, f:ConstraintForeachModel):
        if self.do_copy_level > 0:
            ret = f.clone()
        
            with ConstraintCollector(self, ret):
                for cs in f.constraint_l:
                    cs.accept(self)
        
            self.constraints.append(ret)
        else:
            super().visit_constraint_foreach(f)
        
    def visit_constraint_if_else(self, c:ConstraintIfElseModel):
        from .model_pretty_printer import ModelPrettyPrinter
        if self.do_copy_level > 0:
            ret = ConstraintIfElseModel(self.expr(c.cond))
           
            ret.true_c = ConstraintScopeModel() 
            with ConstraintCollector(self, ret.true_c):
                for cs in c.true_c.constraint_l:
                    cs.accept(self)
                
            if c.false_c is not None:
                ret.false_c = ConstraintScopeModel() 
                with ConstraintCollector(self, ret.false_c):
                    c.false_c.accept(self)

            self.constraints.append(ret)
        else:
            super().visit_constraint_if_else(c)
        
    def visit_constraint_implies(self, c:ConstraintImpliesModel):
        if self.do_copy_level > 0:
            ret = ConstraintImpliesModel(self.expr(c.cond))
        
            with ConstraintCollector(self, ret):
                for cs in c.constraint_l:
                    cs.accept(self)
        
            self.constraints.append(ret)
        else:
            super().visit_constraint_implies(c)
            
    def visit_constraint_inline_scope(self, c : ConstraintInlineScopeModel):
        if self.do_copy_level > 0:
            ret = ConstraintInlineScopeModel()
            
            with ConstraintCollector(self, ret):
                for c in c.constraint_l:
                    c.accept(self)
           
            self.constraints.append(ret)
        else:
            super().visit_constraint_inline_scope(c)
        
    def visit_constraint_soft(self, c:ConstraintSoftModel):
        if self.do_copy_level > 0:
            ret = ConstraintSoftModel(self.expr(c.expr))
            self.constraints.append(ret)
        else:
            super().visit_constraint_soft(c)
        
    def visit_constraint_unique(self, c:ConstraintUniqueModel):
        if self.do_copy_level > 0:
            self.constraints.append(c.clone())
        else:
            super().visit_constraint_unique(c)
        
    def visit_expr_bin(self, e:ExprBinModel):
        from .model_pretty_printer import ModelPrettyPrinter
        if self.do_copy_level > 0:
            self._expr = ExprBinModel(
                self.expr(e.lhs),
                e.op,
                self.expr(e.rhs))
        else:
            super().visit_expr_bin(e)
            
    def visit_expr_cond(self, e : ExprCondModel):
        if self.do_copy_level > 0:
            self._expr = ExprCondModel(
                self.expr(e.cond_e),
                self.expr(e.true_e),
                self.expr(e.false_e))
        else:
            super().visit_expr_cond(e)
        
    def visit_expr_fieldref(self, e):
        # Default to pass-through
        if self.do_copy_level > 0:
            self._expr = e
        else:
            super().visit_expr_fieldref(e)
            
    def visit_expr_indexed_fieldref(self, e):
        if self.do_copy_level > 0:
            self._expr = e
        else:
            super().visit_expr_indexed_fieldref(e)
            
    def visit_expr_range(self, r):
        if self.do_copy_level > 0:
            self._expr = ExprRangeModel(
                self.expr(r.lhs),
                None if r.rhs is None else self.expr(r.rhs))
        else:
            super().visit_expr_range(r)
    
    def visit_expr_rangelist(self, r):
        if self.do_copy_level > 0:
            rl = []
            for ri in r.rl:
                rl.append(self.expr(ri))
            self._expr = ExprRangelistModel(rl)
        else:
            super().visit_expr_rangelist(r)
            
    def visit_expr_in(self, e):
        if self.do_copy_level > 0:
            self._expr = ExprInModel(
                self.expr(e.lhs),
                self.expr(e.rhs))
        else:
            super().visit_expr_in(e)
        
    def visit_expr_literal(self, e):
        if self.do_copy_level > 0:
            self._expr = e
        else:
            super().visit_expr_literal(e)
            
    def visit_expr_unary(self, e : ExprUnaryModel):
        if self.do_copy_level > 0:
            self._expr = ExprUnaryModel(
                e.op,
                self.expr(e.expr))
        else:
            super().visit_expr_unary(e)
        
    def visit_expr_array_subscript(self, s):
        if self.do_copy_level > 0:
            self._expr = ExprArraySubscriptModel(
                self.expr(s.lhs),
                self.expr(s.rhs))
        else:
            super().visit_expr_array_subscript(s)
            
        
    def expr(self, e):
        self._expr = None
        e.accept(self)
        return self._expr
        