'''
Created on Aug 9, 2020

@author: ballance
'''
from vsc.model.constraint_inline_scope_model import ConstraintInlineScopeModel
from vsc.model.model_visitor import ModelVisitor
from vsc.visitors.constraint_override_visitor import ConstraintOverrideVisitor
from vsc.model.constraint_expr_model import ConstraintExprModel
from vsc.model.expr_in_model import ExprInModel
from vsc.model.expr_rangelist_model import ExprRangelistModel
from vsc.model.expr_literal_model import ExprLiteralModel
from vsc.model.expr_range_model import ExprRangeModel
from vsc.model.constraint_implies_model import ConstraintImpliesModel
from vsc.model.expr_bin_model import ExprBinModel
from vsc.model.bin_expr_type import BinExprType
from vsc.model.expr_unary_model import ExprUnaryModel
from vsc.model.unary_expr_type import UnaryExprType
from vsc.model.constraint_soft_model import ConstraintSoftModel
import random
from vsc.visitors.model_pretty_printer import ModelPrettyPrinter
from vsc.model.constraint_dist_scope_model import ConstraintDistScopeModel


class DistConstraintBuilder(ConstraintOverrideVisitor):
    
    def __init__(self, seed):
        super().__init__()
        self.seed = seed
        self.rng = random.Random(self.seed)

    @staticmethod        
    def build(seed, fm):
        builder = DistConstraintBuilder(seed)
        fm.accept(builder)
        
    def visit_constraint_dist(self, c):
        # We replace the dist constraint with an equivalent 
        # set of hard and soft constraints
        scope = ConstraintDistScopeModel(c)
        
        ranges = ExprRangelistModel()
        for w in c.weights:        
            if w.rng_rhs is not None:
                # two-value range
                ranges.add_range(ExprRangeModel(w.rng_lhs, w.rng_rhs))
            else:
                # single value
                ranges.add_range(w.rng_lhs)
        
        # First, create an 'in' constraint to restrict 
        # values to the appropriate value set
        in_c = ConstraintExprModel(
            ExprInModel(c.lhs, ranges))
        scope.addConstraint(in_c)
        
        # Now, we need to add exclusion constraints for any
        # zero weights
        # (!w) -> (lhs != [val])
        # (!w) -> (lns not in [rng])
        for w in c.weights:
            if w.rng_rhs is not None:
                scope.addConstraint(ConstraintImpliesModel(
                    ExprBinModel(
                        w.weight,
                        BinExprType.Eq,
                        ExprLiteralModel(0, False, 8)),
                    [
                        ConstraintExprModel(
                            ExprUnaryModel(
                                UnaryExprType.Not,
                                    ExprBinModel(
                                        ExprBinModel(
                                            c.lhs,
                                            BinExprType.Ge,
                                            w.rng_lhs),
                                    BinExprType.And,
                                        ExprBinModel(
                                            c.lhs,
                                            BinExprType.Le,
                                            w.rng_rhs))))
                    ]))
            else:
                scope.addConstraint(ConstraintImpliesModel(
                    ExprBinModel(
                        w.weight,
                        BinExprType.Eq,
                        ExprLiteralModel(0, False, 8)),
                    [
                        ExprUnaryModel(
                            UnaryExprType.Not,
                            ExprBinModel(
                                c.lhs,
                                BinExprType.Eq,
                                w.rng_lhs))
                    ]))

        # Form a list of non-zero weighted tuples of weight/range
        # Sort in ascending order
        weight_l = []                
        total_w = 0
        for i,w in enumerate(c.weights):
            weight = int(w.weight.val())
            total_w += weight
            if weight > 0:
                weight_l.append((weight, i))
        weight_l.sort(key=lambda w:w[0])
        
        seed_v = self.rng.randint(1, total_w)
        
        # Find the first range 
        i = 0
        while i < len(weight_l):
            seed_v -= weight_l[i][0]
            
            if seed_v <= 0:
                break
                
            i += 1

        if i >= len(weight_l):
            i = len(weight_l)-1

        scope.target_range = weight_l[i][1]            
        target_w = c.weights[weight_l[i][1]]
        dist_soft_c = None
        if target_w.rng_rhs is not None:
            dist_soft_c = ConstraintSoftModel(
                ExprBinModel(
                    ExprBinModel(
                        c.lhs,
                        BinExprType.Ge,
                        target_w.rng_lhs),
                    BinExprType.And,
                    ExprBinModel(
                        c.lhs,
                        BinExprType.Le,
                        target_w.rng_rhs)))
        else:
            dist_soft_c = ConstraintSoftModel(
                ExprBinModel(
                    c.lhs,
                    BinExprType.Eq,
                    target_w.rng_lhs))
        # Give dist constraints a high priority to allow
        # them to override all user-defined soft constraints
        dist_soft_c.priority = 1000000
        scope.set_dist_soft_c(dist_soft_c)
        
        self.override_constraint(scope)
        
        