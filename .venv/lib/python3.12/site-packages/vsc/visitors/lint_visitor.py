'''
Created on Jul 19, 2021

@author: mballance
'''
from vsc.model.model_visitor import ModelVisitor
from vsc.model.expr_bin_model import ExprBinModel
from vsc.visitors.is_nonrand_expr_visitor import IsNonRandExprVisitor
from vsc.model.source_info import SourceInfo

class LintVisitor(ModelVisitor):
    
    def __init__(self):
        self.ret = ""
        pass
    
    def lint(self, fields, constraints):
        self.ret = ""
        for f in fields:
            f.accept(self)
        for c in constraints:
            c.accept(self)
            
        return self.ret
    
    def visit_expr_bin(self, e:ExprBinModel):
        # Each side could be
        # - rand
        # - resolved
        ModelVisitor.visit_expr_bin(self, e)
        
        lhs_nonrand = IsNonRandExprVisitor().is_nonrand(e.lhs)
        rhs_nonrand = IsNonRandExprVisitor().is_nonrand(e.rhs)
        
        if lhs_nonrand and not rhs_nonrand:
            lhs_v = e.lhs.val()
            rhs_w = e.rhs.width()
            
#            print("lhs_v=%d rhs_w=%d" % (int(lhs_v), rhs_w))
        elif rhs_nonrand and not lhs_nonrand:
            rhs_v = e.rhs.val()
            lhs_w = e.lhs.width()
            lhs_s = e.lhs.is_signed()
            
#            print("rhs_v=%d lhs_w=%d lhs_s=%d" % (int(rhs_v), lhs_w, int(lhs_s)))
            
            if lhs_s:
                pass
            else:
                lhs_max = (1 << lhs_w) - 1
                
                if rhs_v > lhs_max:
                    self.ret += "%s: %d is out-of-bounds for domain %d..%d\n" % (
                        SourceInfo.toString(e.srcinfo), int(rhs_v), 0, lhs_max)

