'''
Created on Apr 28, 2020

@author: ballance
'''
from vsc.model.field_composite_model import FieldCompositeModel
'''
Created on Apr 28, 2020

@author: ballance
'''

from _io import StringIO

import vsc.model as vm
from vsc.model.constraint_dist_model import ConstraintDistModel
from vsc.model.constraint_expr_model import ConstraintExprModel
from vsc.model.constraint_foreach_model import ConstraintForeachModel
from vsc.model.constraint_solve_order_model import ConstraintSolveOrderModel
from vsc.model.covergroup_model import CovergroupModel
from vsc.model.coverpoint_bin_array_model import CoverpointBinArrayModel
from vsc.model.coverpoint_bin_collection_model import CoverpointBinCollectionModel
from vsc.model.coverpoint_bin_single_range_model import CoverpointBinSingleRangeModel
from vsc.model.coverpoint_model import CoverpointModel
from vsc.model.dist_weight_expr_model import DistWeightExprModel
from vsc.model.field_array_model import FieldArrayModel
from vsc.model.field_scalar_model import FieldScalarModel
from vsc.model.model_visitor import ModelVisitor
from vsc.model.rangelist_model import RangelistModel
from vsc.model.unary_expr_type import UnaryExprType


class ModelPrettyPrinter(ModelVisitor):

    def __init__(self):
        self.out = StringIO()
        self.ind = ""
        self.print_values = False
        
    def do_print(self, m, print_values=False, show_exp=False):
        self.ind = ""
        self.print_values = print_values
        self.show_exp = show_exp
        self.out = StringIO()
        
        m.accept(self)
        
        return self.out.getvalue()
    
    @staticmethod
    def print(m, print_values=False, show_exp=False):
        p = ModelPrettyPrinter()
        return p.do_print(m, print_values, show_exp)
    
    def write(self, s):
        self.out.write(s)
        
    def writeln(self, l):
        self.out.write(self.ind + l + "\n")
        
    def inc_indent(self):
        self.ind += " "*4
        
    def dec_indent(self):
        self.ind = self.ind[4:]
        
    def visit_composite_field(self, f : FieldCompositeModel):
        name = f.name if f.name is not None else "<anonymous>"
        self.writeln(name + " {")
        self.inc_indent()
        super().visit_composite_field(f)
        self.dec_indent()
        self.writeln("}")
    
    def visit_constraint_block(self, c:vm.ConstraintBlockModel):
        self.writeln("constraint " + c.name + " {")
        self.inc_indent()
        for stmt in c.constraint_l:
            stmt.accept(self)
        self.dec_indent()
        self.writeln("}")
        
    def visit_constraint_dist(self, d : ConstraintDistModel):
        self.write(self.ind)
        d.lhs.accept(self)
        self.write(" dist { ")
        for i in range(len(d.weights)):
            if i > 0:
                self.write(", ")
            d.weights[i].accept(self)
        self.write("}\n")
        
    def visit_dist_weight(self, w : DistWeightExprModel):
        if w.rng_rhs is not None:
            self.write("[")
            w.rng_lhs.accept(self)
            self.write(":")
            w.rng_rhs.accept(self)
            self.write("]")
        else:
            w.rng_lhs.accept(self)
            
        self.write(" : ")
        w.weight.accept(self)
        
    def visit_constraint_expr(self, c:ConstraintExprModel):
        self.write(self.ind)
        c.e.accept(self)
        self.write(";\n")
        
    def visit_constraint_foreach(self, f:ConstraintForeachModel):
        self.write(self.ind + "foreach (")
        f.lhs.accept(self)
        self.write("[i]) {\n")
        self.inc_indent()
        for s in f.constraint_l:
            s.accept(self)
        self.dec_indent()
        self.writeln("}")
        
    def visit_constraint_if_else(self, c:vm.ConstraintIfElseModel):
        self.write(self.ind + "if (")
        c.cond.accept(self)
        self.write(") {\n")
        self.inc_indent()
        c.true_c.accept(self)
        self.dec_indent()
        
        if c.false_c is not None:
            self.writeln("} else {")
            self.inc_indent()
            c.false_c.accept(self)
            self.dec_indent()
            
        self.writeln("}")
        
    def visit_constraint_implies(self, c:vm.ConstraintImpliesModel):
        self.write(self.ind)
        c.cond.accept(self)
        self.write(" -> {")

        for sc in c.constraint_l:
            sc.accept(self)
            
        self.write("}\n")
        
    def visit_constraint_solve_order(self, c:ConstraintSolveOrderModel):
        self.write(self.ind)
        self.write("solve ")
        for i, b in enumerate(c.before_l):
            if i > 0:
                self.write(",")
            self.write(b.name)
        self.write(" before ")
        for i, a in enumerate(c.after_l):
            if i > 0:
                self.write(",")
            self.write(a.name)
        self.write("\n")
        
    def visit_covergroup(self, cg : CovergroupModel):
        self.writeln("covergroup " + cg.name)
        self.inc_indent()
        for cp in cg.coverpoint_l:
            cp.accept(self)
        self.dec_indent()
        
    def visit_coverpoint(self, cp : CoverpointModel):
        self.writeln("coverpoint " + cp.name)
        self.inc_indent()
        for b in cp.bin_model_l:
            b.accept(self)
        self.dec_indent()
        
    def visit_coverpoint_bin_array(self, bn : CoverpointBinArrayModel):
        self.writeln("bin_array " + bn.name)
        
    def visit_coverpoint_bin_collection(self, bn : CoverpointBinCollectionModel):
        self.writeln("bin_collection " + bn.name)
        self.inc_indent()
        for b in bn.bin_l:
            b.accept(self);
        self.dec_indent()
        
    def visit_coverpoint_bin_single_range(self, bn : CoverpointBinSingleRangeModel):
        self.writeln("bin_single_range " + bn.name + " " + str(bn.target_val_low) + " .. " + str(bn.target_val_high))
        
    def visit_expr_array_subscript(self, s):
        s.lhs.accept(self)
        self.write("[")
        s.rhs.accept(self)
        self.write("]")
        
    def visit_expr_array_sum(self, s):
        if self.show_exp:
            s.expr().accept(self)
        else:
            self.write(s.arr.fullname)
            self.write(".sum")

    def visit_expr_bin(self, e:vm.ExprBinModel):
        if e.lhs is None or e.rhs is None:
            print("op: " + str(e.op))
        self.write("(")
        e.lhs.accept(self)
        self.write(" " + vm.BinExprType.toString(e.op) + " ")
        e.rhs.accept(self)
        self.write(")")
        
    def visit_expr_in(self, e:vm.ExprInModel):
        e.lhs.accept(self)
        self.write(" in [")
        for i, r in enumerate(e.rhs.rl):
            if i > 0:
                self.write(", ")
            r.accept(self)
                
        self.write("]")
        
    def visit_expr_literal(self, e : vm.ExprLiteralModel):
        self.write(str(int(e.val())))
        
    def visit_expr_indexed_fieldref(self, e):
        e.root.accept(self)
        self.write(".")
        for i,idx in enumerate(e.idx_t):
            self.write("[%d]" % idx)
        
    def visit_expr_fieldref(self, e : vm.ExprFieldRefModel):
        if self.print_values and hasattr(e.fm, "is_used_rand") and not e.fm.is_used_rand:
            if isinstance(e.fm, FieldArrayModel):
                self.write("[")
                for i, f in enumerate(e.fm.field_l):
                    if i > 0:
                        self.write(", ")
                    self.write(str(int(f.get_val())))
                self.write("]")
            else:
                self.write(e.fm.fullname + "(" + str(int(e.fm.get_val())) + ")")
        else:
            self.write(e.fm.fullname)
        
    def visit_expr_unary(self, e : vm.ExprUnaryModel):
        self.write(UnaryExprType.toString(e.op))
        self.write("(")
        e.expr.accept(self)
        self.write(")")
        
    def visit_expr_range(self, r):
        r.lhs.accept(self)
        self.write("..")
        r.rhs.accept(self)
        
    def visit_rangelist(self, r : RangelistModel):
        for re in r.range_l:
            if re[0] == re[1]:
                self.write(str(re[0]))
            else:
                self.write(str(re[0]) + ".." + str(re[1]))
        
    def visit_scalar_field(self, f:FieldScalarModel):
        f_str = ""
        if f.is_used_rand:
            f_str += "rand "
        if f.is_signed:
            f_str += "signed "
        else:
            f_str += "unsigned "
        f_str += "[" + str(f.width) + "] " + f.fullname
        self.writeln(f_str)

