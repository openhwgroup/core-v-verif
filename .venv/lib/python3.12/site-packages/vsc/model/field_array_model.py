'''
Created on May 16, 2020

@author: ballance
'''
from vsc.model.field_scalar_model import FieldScalarModel
from vsc.model.field_composite_model import FieldCompositeModel
from vsc.model.expr_fieldref_model import ExprFieldRefModel
from vsc.model.expr_bin_model import ExprBinModel
from vsc.model.bin_expr_type import BinExprType
from vsc.model.expr_literal_model import ExprLiteralModel
from vsc.model.enum_field_model import EnumFieldModel

class FieldArrayModel(FieldCompositeModel):
    """All arrays are processed as if they were variable size."""
    
    def __init__(self, 
                 name, 
                 type_t,
                 is_scalar,
                 enums,
                 width,
                 is_signed,
                 is_rand,
                 is_rand_sz):
        super().__init__(name, is_rand)
        # width and is_signed only needed for scalar fields
        self.type_t = type_t
        self.is_enum = (enums is not None)
        self.enums = enums
        self.is_scalar = is_scalar
        self.width = width
        self.is_signed = is_signed
        self.is_rand_sz = is_rand_sz
        
        # Holds a cached version of the sum constraint
        self.sum_expr_btor = None
        self.sum_expr = None
        
        # Holds a cached version of the sum constraint
        self.product_expr_btor = None
        self.product_expr = None
        
        self.size = FieldScalarModel(
            "size",
            32,
            False,
            is_rand_sz)
        self.size.parent = self
        self._set_size(0)
        
    def append(self, fm):
        super().add_field(fm)
        self._set_size(len(self.field_l))
        fm.is_declared_rand = self.is_declared_rand
        fm.rand_mode = self.is_declared_rand
        self.name_elems()
        
    def clear(self):
        self.field_l.clear()
        self._set_size(0)

    def pop(self, idx=0):
        self.field_l.pop(idx)
        self._set_size(len(self.field_l))
        self.name_elems()
        
        
    def _set_size(self, sz):
#        self.size.set_used_rand(False)
        if sz != int(self.size.get_val()):
            self.size.set_val(sz)
            self.sum_expr = None
            self.sum_expr_btor = None
            self.product_expr = None
            self.product_expr_btor = None
        
    def name_elems(self):
        """Apply an index-based name to all fields"""
        for i,f in enumerate(self.field_l):
            f.name = self.name + "[" + str(i) + "]"
        
    def pre_randomize(self):
        # Set the size field for arrays that don't
        # have a random size
        if self.is_rand_sz:
            self.size.set_used_rand(True)
        else:
            self._set_size(len(self.field_l))
        FieldCompositeModel.pre_randomize(self)
        
    def post_randomize(self):
        FieldCompositeModel.post_randomize(self)
        self.sum_expr = None
        self.sum_expr_btor = None
        
    def add_field(self) -> FieldScalarModel:
        fid = len(self.field_l)
        if self.is_enum:
            ret = super().add_field(EnumFieldModel(
                self.name + "[" + str(fid) + "]",
                self.enums,
                self.is_declared_rand))
        else:
            ret = super().add_field(FieldScalarModel(
                self.name + "[" + str(fid) + "]",
                self.width,
                self.is_signed,
                self.is_declared_rand))
        # Update the size
        self._set_size(len(self.field_l))
        return ret
        
    def build(self, builder):
        # Called before randomization
        self._set_size(len(self.field_l))
        super().build(builder)
        
#    def set_used_rand(self, is_rand, level=0):
#        if self.is_rand_sz:
#            self.size.set_used_rand(is_rand)
#        FieldCompositeModel.set_used_rand(self, is_rand, level=level)
    def set_used_rand(self, is_rand, level=0):
        super().set_used_rand(is_rand, level)
        self.size.set_used_rand(is_rand, level+1)
        
    def get_sum_expr(self):
        if self.sum_expr is None:
            # Build

            # Compute clog2 of overflow term to 
            # ensure that we properly size the result
            # to avoid overflow            
            result_bits = self.type_t.width
            overflow_val = int(self.size.get_val())-1
            
            while overflow_val > 0:
                result_bits += 1
                overflow_val >>= 1
                
            # Force the result to be 32-bit, in order to 
            # match user expectation
            ret = ExprLiteralModel(0, self.is_signed, result_bits)
            for i in range(int(self.size.get_val())):
                f = self.field_l[i]
                ret = ExprBinModel(
                    ret,
                    BinExprType.Add,
                    ExprFieldRefModel(f))
                
            self.sum_expr = ret
            
        return self.sum_expr
    
    def get_sum_width(self):
        result_bits = self.type_t.width
        overflow_val = int(self.size.get_val())-1
            
        while overflow_val > 0:
            result_bits += 1
            overflow_val >>= 1

        return result_bits
        
    def build_sum_expr(self, btor, ctx_width=-1):
        if self.sum_expr_btor is None:
            self.sum_expr_btor = self.get_sum_expr().build(btor, ctx_width)
        return self.sum_expr_btor
    
    def get_product_expr(self):
        if self.product_expr is None:
            # Build
            
            # Force the result to be 32-bit, in order to 
            # match user expectation
            if int(self.size.get_val()) == 0:
                ret = ExprLiteralModel(0, self.is_signed, 64)
            else:
                ret = ExprLiteralModel(1, self.is_signed, 64)
            for i in range(int(self.size.get_val())):
                f = self.field_l[i]
                ret = ExprBinModel(
                    ret,
                    BinExprType.Mul,
                    ExprFieldRefModel(f))
                
            self.product_expr = ret
            
        return self.product_expr
        
    def build_product_expr(self, btor, ctx_width=-1):
        if self.product_expr_btor is None:
            self.product_expr_btor = self.get_product_expr().build(btor, ctx_width)
        return self.product_expr_btor    
        
    def accept(self, v):
        v.visit_field_scalar_array(self)
