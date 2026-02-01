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

# Created on Jul 23, 2019
#
# @author: ballance


from vsc.impl.ctor import push_constraint_scope, push_constraint_stmt, pop_expr, \
    pop_constraint_scope, in_constraint_scope, last_constraint_stmt, push_expr, \
    push_foreach_arr, pop_foreach_arr, constraint_scope_depth, in_srcinfo_mode
from vsc.model.constraint_dist_model import ConstraintDistModel
from vsc.model.constraint_foreach_model import ConstraintForeachModel
from vsc.model.constraint_if_else_model import ConstraintIfElseModel
from vsc.model.constraint_implies_model import ConstraintImpliesModel
from vsc.model.constraint_scope_model import ConstraintScopeModel
from vsc.model.constraint_soft_model import ConstraintSoftModel
from vsc.model.constraint_solve_order_model import ConstraintSolveOrderModel
from vsc.model.constraint_unique_model import ConstraintUniqueModel
from vsc.model.dist_weight_expr_model import DistWeightExprModel
from vsc.model.expr_array_subscript_model import ExprArraySubscriptModel
from vsc.model.expr_dynref_model import ExprDynRefModel
from vsc.model.expr_fieldref_model import ExprFieldRefModel
from vsc.model.expr_indexed_field_ref_model import ExprIndexedFieldRefModel
from vsc.model.field_scalar_model import FieldScalarModel
from vsc.types import to_expr, expr, type_base, rng
from vsc.visitors.expr2fieldtype_visitor import Expr2FieldTypeVisitor
from vsc.model.source_info import SourceInfo


class constraint_t(object):
    
    def __init__(self, c):
        self.c = c
        self.enabled = True
        self.model = None
        self.srcinfo = None
        pass
    
    def constraint_mode(self, en):
        self.enabled = en
        if self.model is not None:
            self.model.set_constraint_enabled(en)
            
    def set_model(self, m):
        self.model = m
        self.model.set_constraint_enabled(self.enabled)
            
    
    def elab(self):
        print("elab")
        
class dynamic_constraint_t(object):
    
    def __init__(self, c):
        self.c = c
        self.model = None
        self.srcinfo = None
        
    def set_model(self, m):
        self.model = m
        
    def __call__(self):
        return expr(ExprDynRefModel(self.model))

    class call_closure(object):
        
        def __init__(self, c, *args, **kwargs):
            self.c = c
            self.args = args
            self.kwargs = kwargs
            
        def __enter__(self):
            self.c(*self.args, **self.kwargs)
        
        def __exit__(self, t, v, tb):
            pass
        

def dynamic_constraint(c):
    ret = dynamic_constraint_t(c)
    
    # Capture source info, since it's only
    # captured once during loading
    ret.srcinfo = SourceInfo.mk()
    return ret

def constraint(c):
    ret = constraint_t(c)
    
    # Capture source info, since it's only
    # captured once during loading
    ret.srcinfo = SourceInfo.mk()
    return ret

class weight(object):
    
    def __init__(self, val, w):
        rng_lhs_e = None
        rng_rhs_e = None
    
        if isinstance(val, (list,tuple)):
            if len(val) != 2:
                raise Exception("Weight range must have two elements")
            to_expr(val[0])
            rng_lhs_e = pop_expr()
            to_expr(val[1])
            rng_rhs_e = pop_expr()
        elif isinstance(val, rng):
            rng_lhs_e = val.low
            rng_rhs_e = val.high 
        else:
            to_expr(val)
            rng_lhs_e = pop_expr()
        to_expr(w)
        w_e = pop_expr()
    
        self.weight_e = DistWeightExprModel(
            rng_lhs_e,
            rng_rhs_e,
            w_e)
    

def dist(lhs, weights):
    """Applies distribution weights to the specified field"""
    
    to_expr(lhs)
    lhs_e = pop_expr()
    
    weight_l = []
    for w in weights:
        if not isinstance(w, weight):
            raise Exception("Weight specifications must of type 'vsc.weight', not " + 
                            str(w))
        weight_l.append(w.weight_e)
        
    c = ConstraintDistModel(lhs_e, weight_l)
    if in_srcinfo_mode():
        c.srcinfo = SourceInfo.mk()
        
    push_constraint_stmt(c)
    

class if_then(object):

    def __init__(self, e):
        if not in_constraint_scope():
            raise Exception("Attempting to use if_then constraint outside constraint scope")
        
        to_expr(e)
        self.stmt = ConstraintIfElseModel(pop_expr())
        if in_srcinfo_mode():
            self.stmt.srcinfo = SourceInfo.mk()
        push_constraint_stmt(self.stmt)
        
    def __enter__(self):
        self.stmt.true_c = ConstraintScopeModel()
        push_constraint_scope(self.stmt.true_c)
        
    def __exit__(self, t, v, tb):
        pop_constraint_scope()
        
        
class else_if(object):

    def __init__(self, e):
        self.stmt = None
        
        if not in_constraint_scope():
            raise Exception("Attempting to use if_then constraint outside constraint scope")
        
        last_stmt = last_constraint_stmt()
        if last_stmt == None or not isinstance(last_stmt, ConstraintIfElseModel):
            raise Exception("Attempting to use else_if where it doesn't follow if_then")
        
        to_expr(e)
        # Need to find where to think this in
        while last_stmt.false_c != None:
            last_stmt = last_stmt.false_c
            
        self.stmt = ConstraintIfElseModel(pop_expr())
        if in_srcinfo_mode():
            self.stmt.srcinfo = SourceInfo.mk()
        last_stmt.false_c = self.stmt
        
    def __enter__(self):
        if self.stmt is not None:
            self.stmt.true_c = ConstraintScopeModel()
            push_constraint_scope(self.stmt.true_c)
        
    def __exit__(self, t, v, tb):
        pop_constraint_scope()
        
class else_then_c(object):

    def __init__(self):
        pass
    
    def __call__(self):
        return self
        
    def __enter__(self):
        if not in_constraint_scope():
            raise Exception("Attempting to use if_then constraint outside constraint scope")
        
        last_stmt = last_constraint_stmt()
        if last_stmt == None or not isinstance(last_stmt, ConstraintIfElseModel):
            raise Exception("Attempting to use else_then where it doesn't follow if_then/else_if")
        
        # Need to find where to think this in
        while last_stmt.false_c != None:
            last_stmt = last_stmt.false_c
            
        stmt = ConstraintScopeModel()
        last_stmt.false_c = stmt
        push_constraint_scope(stmt)
        
    def __exit__(self, t, v, tb):
        pop_constraint_scope()

else_then = else_then_c()

class implies(object):

    def __init__(self, e):
        if not in_constraint_scope():
            raise Exception("Attempting to use if_then constraint outside constraint scope")
        
        to_expr(e)
        self.stmt = ConstraintImpliesModel(pop_expr())
        if in_srcinfo_mode():
            self.stmt.srcinfo = SourceInfo.mk()
        
    def __enter__(self):
        push_constraint_stmt(self.stmt)
        push_constraint_scope(self.stmt)
        
    def __exit__(self, t, v, tb):
        pop_constraint_scope()
        
def soft(e):
    
    to_expr(e)
    em = pop_expr()
    c = ConstraintSoftModel(em)
    c.srcinfo = em.srcinfo
    push_constraint_stmt(c)
    

def unique(*args):
    expr_l = []
    for i in range(-1, -(len(args)+1), -1):
        to_expr(args[i])
        expr_l.insert(0, pop_expr())

    c = ConstraintUniqueModel(expr_l)
    if in_srcinfo_mode():
        c.srcinfo = SourceInfo.mk()
    push_constraint_stmt(c)
    
class forall(object):
    
    def __init__(self, target_type):
        self.target_type = target_type
        pass
    
    def __enter__(self):
        pass
    
    def __exit__(self, t, v, tb):
        pass
    
class foreach(object):
    
    class idx_term_c(type_base):
        def __init__(self, index):
            super().__init__(32, False)
            self.index = index
        def to_expr(self):
            return expr(ExprFieldRefModel(self.index))
        
    class it_term_c(type_base):
        def __init__(self, em):
            super().__init__(32, False)
            self.em = em
        def to_expr(self):
            return expr(self.em)
        
        def __getattr__(self, aname):
            em = object.__getattribute__(self, "em")
            
            # This pops 'this expr' off the stack, so we can
            # replace it with an extended expression
#            pop_expr()
          
            ret = None
            if isinstance(em, ExprArraySubscriptModel):
                # TODO: Need to get the core type
                fm = None
                if isinstance(em.lhs, ExprIndexedFieldRefModel):
                    fm = em.lhs.get_target()
                elif isinstance(em.lhs, ExprFieldRefModel):
                    fm = em.lhs.fm
                else:
                    raise Exception("Unsupported path-chaining expression " + str(em.lhs))
                
                if aname in fm.type_t.field_id_m.keys():
                    idx = fm.type_t.field_id_m[aname]
                    ret = expr(ExprIndexedFieldRefModel(em, [idx]))
                else:
                    raise Exception("Type %s does not contain a field \"%s\"" % (
                        fm.type_t.name, aname))
            else:
                raise Exception("Expression getattribute access on non-subscript")
    
            return ret        
    
    def __init__(self, l, it=None, idx=None):
        self.stmt = None
        
        if it is None and idx is None:
            # Default: use it
            it = True
            idx = False
        else:
            # One or more are specified
            if idx is None:
                idx = False
            if it is None:
                it = False
                
        if not idx and not it:
            raise Exception("Neither it nor idx specified")

        # Form an expression to the array        
        to_expr(l)
        e = pop_expr()

        self.arr_ref_e = e
        self.elem_t = Expr2FieldTypeVisitor().fieldtype(e)
            
        self.it = it
        self.idx = idx
        
        if not in_constraint_scope():
            raise Exception("Attempting to use foreach constraint outside constraint scope")

        self.stmt = ConstraintForeachModel(e)
        if in_srcinfo_mode():
            self.stmt.srcinfo = SourceInfo.mk()
        
    def __enter__(self):
        push_constraint_stmt(self.stmt)
        push_constraint_scope(self.stmt)

        idx_term = foreach.idx_term_c(self.stmt.index)
        it_term = foreach.it_term_c(ExprArraySubscriptModel(
            self.arr_ref_e,
            ExprFieldRefModel(self.stmt.index)))
        
        if self.idx and self.it:
            return (idx_term, it_term)
        else:
            if self.it:
                return it_term
            else:
                return idx_term

    def __exit__(self, t, v, tb):
        pop_constraint_scope()
       

def solve_order(before, after):
    if constraint_scope_depth() != 1:
        raise Exception("solve_before can only be used at a constraint top level")

    before_l = []
    after_l = []
    
    if isinstance(before, list):
        for b in before:
            to_expr(b)
            b_e = pop_expr()
            if not isinstance(b_e, ExprFieldRefModel):
                raise Exception("Parameter " + str(b) + " is not a field reference")
            before_l.append(b_e.fm)
    else:
        to_expr(before)
        before_e = pop_expr()
        
        if not isinstance(before_e, ExprFieldRefModel):
            raise Exception("Parameter " + str(before) + " is not a field reference")
        before_l.append(before_e.fm)
    
    if isinstance(after, list):
        for a in after:
            to_expr(a)
            a_e = pop_expr()
            if not isinstance(a_e, ExprFieldRefModel):
                raise Exception("Parameter " + str(a) + " is not a field reference")
            before_l.append(a_e.fm)
    else:
        to_expr(after)
        after_e = pop_expr()
        if not isinstance(after_e, ExprFieldRefModel):
            raise Exception("Parameter " + str(after) + " is not a field reference")
        after_l.append(after_e.fm)

    c = ConstraintSolveOrderModel(before_l, after_l)
    if in_srcinfo_mode():
        c.srcinfo = SourceInfo.mk()
    push_constraint_stmt(c)


    
    
        
