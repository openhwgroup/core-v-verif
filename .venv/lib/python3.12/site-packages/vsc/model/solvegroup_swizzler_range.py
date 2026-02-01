'''
Created on Sep 18, 2021

@author: mballance
'''
import random

from vsc.model.bin_expr_type import BinExprType
from vsc.model.expr_bin_model import ExprBinModel
from vsc.model.expr_fieldref_model import ExprFieldRefModel
from vsc.model.expr_literal_model import ExprLiteralModel
from vsc.model.expr_model import ExprModel
from vsc.model.field_scalar_model import FieldScalarModel
from vsc.model.variable_bound_model import VariableBoundModel


class SolveGroupSwizzlerRange(object):
    
    def __init__(self, solve_info):
        self.debug = 0
        self.solve_info = solve_info
        pass
    
    def swizzle(self, 
                btor, 
                rs, 
                bound_m):
        if self.debug > 0:
            print("--> swizzle_randvars")

        swizzled_field = False
        # For each random variable, select a partition with it's known 
        # domain and add the corresponding constraint
        field_l = rs.rand_fields()
            
        if self.debug > 0:
            print("  " + str(len(field_l)) + " fields in randset")
            
        if rs.rand_order_l is not None:
            # Perform an ordered randomization
            for ro_l in rs.rand_order_l:
                swizzled_field |= self.swizzle_field_l(ro_l, rs, bound_m, btor)
        else:
            swizzled_field |= self.swizzle_field_l(rs.rand_fields(), rs, bound_m, btor)
                
#            x += 1
            
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
        if low > high:
            tmp = low
            low = high
            high = tmp

        return random.randint(low,high)
