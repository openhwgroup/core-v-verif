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


from enum import IntEnum, Enum, EnumMeta

from vsc.impl.ctor import push_expr, pop_expr, in_constraint_scope, \
    is_foreach_arr, expr_l, in_srcinfo_mode
from vsc.impl.enum_info import EnumInfo
from vsc.impl.expr_mode import is_expr_mode
from vsc.model.bin_expr_type import BinExprType
from vsc.model.enum_field_model import EnumFieldModel
from vsc.model.expr_array_subscript_model import ExprArraySubscriptModel
from vsc.model.expr_array_sum_model import ExprArraySumModel
from vsc.model.expr_bin_model import ExprBinModel
from vsc.model.expr_fieldref_model import ExprFieldRefModel
from vsc.model.expr_in_model import ExprInModel
from vsc.model.expr_indexed_field_ref_model import ExprIndexedFieldRefModel
from vsc.model.expr_literal_model import ExprLiteralModel
from vsc.model.expr_partselect_model import ExprPartselectModel
from vsc.model.expr_range_model import ExprRangeModel
from vsc.model.expr_rangelist_model import ExprRangelistModel
from vsc.model.expr_unary_model import ExprUnaryModel
from vsc.model.field_array_model import FieldArrayModel
from vsc.model.field_const_array_model import FieldConstArrayModel
from vsc.model.field_scalar_model import FieldScalarModel
from vsc.model.unary_expr_type import UnaryExprType
from vsc.model.value_scalar import ValueScalar, ValueInt


from vsc.impl.expr_mode import get_expr_mode, expr_mode, is_expr_mode
from vsc.model.expr_array_product_model import ExprArrayProductModel
from vsc.visitors.model_pretty_printer import ModelPrettyPrinter
from vsc.model.expr_indexed_dynref_model import ExprIndexedDynRefModel
from vsc.model.source_info import SourceInfo


def unsigned(v, w=-1):
    if w == -1:
        w = 32
    return expr(ExprLiteralModel(v, False, w))

def signed(v, w=-1):
    if w == -1:
        w = 32
    return expr(ExprLiteralModel(v, True, w))

class expr(object):
    def __init__(self, em):
        push_expr(em)
        self.em = em
        
    def bin_expr(self, op, rhs):
        to_expr(rhs)

        rhs_e = pop_expr()
        lhs_e = pop_expr()
       
        e = ExprBinModel(lhs_e, op, rhs_e)
        if in_srcinfo_mode():
            e.srcinfo = SourceInfo.mk(2)
        
        return expr(e)
        
    def __eq__(self, rhs):
        return self.bin_expr(BinExprType.Eq, rhs)
    
    def __ne__(self, rhs):
        return self.bin_expr(BinExprType.Ne, rhs)
    
    def __le__(self, rhs):
        return self.bin_expr(BinExprType.Le, rhs)
    
    def __lt__(self, rhs):
        return self.bin_expr(BinExprType.Lt, rhs)
    
    def __ge__(self, rhs):
        return self.bin_expr(BinExprType.Ge, rhs)
    
    def __gt__(self, rhs):
        return self.bin_expr(BinExprType.Gt, rhs)
    
    def __add__(self, rhs):
        return self.bin_expr(BinExprType.Add, rhs)
    
    def __sub__(self, rhs):
        return self.bin_expr(BinExprType.Sub, rhs)
    
    def __truediv__(self, rhs):
        return self.bin_expr(BinExprType.Div, rhs)
    
    def __floordiv__(self, rhs):
        return self.bin_expr(BinExprType.Div, rhs)
    
    def __mul__(self, rhs):
        return self.bin_expr(BinExprType.Mul, rhs)
    
    def __mod__(self, rhs):
        return self.bin_expr(BinExprType.Mod, rhs)
    
    def __and__(self, rhs):
        return self.bin_expr(BinExprType.And, rhs)
    
    def __or__(self, rhs):
        return self.bin_expr(BinExprType.Or, rhs)
    
    def __xor__(self, rhs):
        return self.bin_expr(BinExprType.Xor, rhs)
    
    def __lshift__(self, rhs):
        return self.bin_expr(BinExprType.Sll, rhs)
    
    def __rshift__(self, rhs):
        return self.bin_expr(BinExprType.Srl, rhs)
    
    def __neg__(self):
        return self.bin_expr(BinExprType.Not, rhs)    
    
    def __invert__(self):
        lhs = pop_expr()
        
        return expr(ExprUnaryModel(UnaryExprType.Not, lhs))
    
    def inside(self, rhs):
        lhs_e = pop_expr()
        
        if isinstance(rhs, rangelist):
            return expr(ExprInModel(lhs_e, rhs.range_l))
        elif isinstance(rhs, list_t):
            return expr(ExprInModel(
                lhs_e,
                ExprRangelistModel(
                    [ExprFieldRefModel(rhs.get_model())])))
        else:
            raise Exception("Unsupported 'inside' argument of type " + str(type(rhs)) + 
                            "expect vsc.rangelist or list_t")

    def outside(self, rhs):
        self.not_inside(rhs)
            
    def not_inside(self, rhs):
        lhs_e = pop_expr()
        
        if isinstance(rhs, rangelist):
            return expr(ExprUnaryModel(
                UnaryExprType.Not,
                ExprInModel(lhs_e, rhs.range_l)))
        elif isinstance(rhs, list_t):
            return expr(ExprUnaryModel(
                UnaryExprType.Not,
                ExprInModel(lhs_e,
                    ExprRangelistModel(
                        [ExprFieldRefModel(rhs.get_model())]))))
        else:
            raise Exception("Unsupported 'not_inside' argument of type " + str(type(rhs)))
        
    def __getitem__(self, k):
        if is_expr_mode():
            if isinstance(k, slice):
                # Part-select on a field expression
                print("k=" + str(k) + " start=" + str(k.start) + " stop=" + str(k.stop))
                
                to_expr(k.start)
                upper = pop_expr()
                to_expr(k.stop)
                lower = pop_expr()
                
                base_e = pop_expr()
                return expr(ExprPartselectModel(base_e, upper, lower))
            else:
                # single value
                to_expr(k)
                idx_e = pop_expr()
                base_e = pop_expr()
                
                return expr_subscript(ExprArraySubscriptModel(
                    base_e,
                    idx_e))
        else:
            raise Exception("Calling __getitem__ on an expr on non-expression context")
        
class dynamic_constraint_proxy(object):
    
    def __init__(self, em):
        self.em = em
        
    def __call__(self):
        return expr(self.em)
    
class expr_subscript(expr):
    def __init__(self, em):
        super().__init__(em)
        
    def __getattr__(self, aname):
        em = object.__getattribute__(self, "em")
        
        # This pops 'this expr' off the stack, so we can
        # replace it with an extended expression
        pop_expr()
      
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
            elif aname in fm.type_t.constraint_dynamic_m.keys():
                idx = fm.type_t.constraint_dynamic_m[aname]
                ret = dynamic_constraint_proxy(ExprIndexedDynRefModel(em, idx))
            else:
                raise Exception("Type %s does not contain a field \"%s\"" % (
                    fm.type_t.name, aname))
        else:
            raise Exception("Expression getattribute access on non-subscript")

        return ret
    
    
class rng(object):
    
    def __init__(self, low, high):
        to_expr(low)
        self.low = pop_expr()
        to_expr(high)
        self.high = pop_expr()
        
class rangelist(object):
    
    def __init__(self, *args):
        if len(args) == 0:
            raise Exception("Empty rangelist specified")

        self.range_l = ExprRangelistModel()
        for i in range(-1,-(len(args)+1), -1):
            a = args[i]
            if isinstance(a, tuple):
                # This needs to be a two-element array
                if len(a) != 2:
                    raise Exception("Range specified with " + str(len(a)) + " elements is invalid. Two elements required")
                to_expr(a[0])
                e0 = pop_expr()
                to_expr(a[1])
                e1 = pop_expr()
                self.range_l.add_range(ExprRangeModel(e0, e1))
            elif isinstance(a, rng):
                self.range_l.add_range(ExprRangeModel(a.low, a.high))
            elif isinstance(a, list):
                for ai in a:
                    to_expr(ai)
                    eai = pop_expr()
                    self.range_l.add_range(eai)
            else:
                to_expr(a)
                e = pop_expr()
                self.range_l.add_range(e)
#            self.range_l.rl.reverse()

                # This needs to be convertioble to a
                
    def __contains__(self, lhs):
        to_expr(lhs)
        return expr(ExprInModel(pop_expr(), self.range_l))
    
    def __invert__(self):
        print("rangelist.__invert__")

def to_expr(t):
    if isinstance(t, expr):
        # This expression is already on the stack
#        push_expr(t.em)
        return t
    elif type(t) == int or type(t) == ValueInt:
        return expr(ExprLiteralModel(int(t), True, 32))
    elif isinstance(type(t), (EnumMeta,IntEnum)):
        return expr(EnumInfo.get(type(t)).e2e(t))
    elif hasattr(t, "to_expr"):
        return t.to_expr()
    elif callable(t):
        raise Exception("TODO: support lambda references")
    else:
        raise Exception("Element \"" + str(t) + "\" isn't recognized, and doesn't provide to_expr (type=%s)" % str(type(t)))
    
    
class field_info(object):
    """Model-specific information about the field"""
    def __init__(self, is_composite=False):
        # a non-negative id means that this field
        # can be referenced via an indirect indexed 
        # expression. This is used for coverage of
        # composite fields and for lists
        self.id = -1 
        self.parent = None
        self.root_e = None
        self.is_composite = is_composite
        
        self.name = None
        self.is_rand = False
        self.model = None
        # Specifies whether an ExprIndexedFieldRef should be used
        self.indexed_ref = False
        
    def set_is_rand(self, is_rand):
        self.is_rand = is_rand
        if self.model is not None:
            self.model.is_declared_rand = is_rand
        
class type_base(object):
    """Base type for all primitive-type fields that participate in constraints"""
    
    def __init__(self, width, is_signed, i=0):
        self.width = width
        self.is_signed = is_signed
        self._init_val = i
        self._int_field_info = field_info()
        
    def get_model(self):
        if self._int_field_info.model is None:
            self.build_field_model("<anonymous>")
        return self._int_field_info.model
        
    def build_field_model(self, name):
        self._int_field_info.name = name
        if self._int_field_info.model is None:
            self._int_field_info.model = FieldScalarModel(
                name,
                self.width,
                self.is_signed,
                self._int_field_info.is_rand)
            self.set_val(self._init_val)
        else:
            # Ensure the name matches superstructure
            self._int_field_info.model.name = name
            
        return self._int_field_info.model
    
    def to_expr(self):
        if self._int_field_info.id != -1:
            # A non-negative id means that this field
            # should be referenced indirectly. Follow the
            # parent/child relationships up to construct an
            # index list back to this field
            id_l = []
            fi = self._int_field_info
            
            while fi.parent is not None:
                id_l.insert(0, fi.id)
                fi = fi.parent
                
            return expr(ExprIndexedFieldRefModel(fi.root_e, id_l))
        else:
            return expr(ExprFieldRefModel(self._int_field_info.model))
        
    @property
    def rand_mode(self):
        return self._int_field_info.model.rand_mode
    
    @rand_mode.setter
    def rand_mode(self, v):
        self._int_field_info.model.rand_mode = bool(v)

    @property
    def val(self):
        return int(self.get_model().get_val())
    
    @val.setter
    def val(self, v):
        if self.is_signed:
            # TODO: handle signed masking
            self.get_model().set_val(ValueScalar(int(v)))
        else:
            # Mask the user-specified value
            v = int(v) & ((1 << self.width)-1)
            self.get_model().set_val(ValueScalar(v))
            
    def get_val(self):
        return self.get_model().get_val().toInt()
    
    def set_val(self, val):
        if self.is_signed:
            # TODO: handle signed masking
            self.get_model().set_val(ValueScalar(int(val)))
        else:
            # Mask the user-specified value
            val = int(val) & ((1 << self.width)-1)
            self.get_model().set_val(ValueScalar(val))
        
    def bin_expr(self, op, rhs):
        to_expr(rhs)
        rhs_e = pop_expr()

#        push_expr(ExprFieldRefModel(self._int_field_info.model))
        # Push a reference to this field
        self.to_expr()

        lhs_e = pop_expr()
        
        e = ExprBinModel(lhs_e, op, rhs_e)
        if in_srcinfo_mode():
            e.srcinfo = SourceInfo.mk(2)
        
        return expr(e)

    def __eq__(self, rhs):
        return self.bin_expr(BinExprType.Eq, rhs)
    
    def __ne__(self, rhs):
        return self.bin_expr(BinExprType.Ne, rhs)
    
    def __le__(self, rhs):
        return self.bin_expr(BinExprType.Le, rhs)
    
    def __lt__(self, rhs):
        return self.bin_expr(BinExprType.Lt, rhs)
    
    def __ge__(self, rhs):
        return self.bin_expr(BinExprType.Ge, rhs)
    
    def __gt__(self, rhs):
        return self.bin_expr(BinExprType.Gt, rhs)
    
    def __add__(self, rhs):
        return self.bin_expr(BinExprType.Add, rhs)
    
    def __sub__(self, rhs):
        return self.bin_expr(BinExprType.Sub, rhs)
    
    def __truediv__(self, rhs):
        return self.bin_expr(BinExprType.Div, rhs)
    
    def __floordiv__(self, rhs):
        return self.bin_expr(BinExprType.Div, rhs)
    
    def __mul__(self, rhs):
        return self.bin_expr(BinExprType.Mul, rhs)
    
    def __mod__(self, rhs):
        return self.bin_expr(BinExprType.Mod, rhs)
    
    def __and__(self, rhs):
        return self.bin_expr(BinExprType.And, rhs)
    
    def __or__(self, rhs):
        return self.bin_expr(BinExprType.Or, rhs)
    
    def __xor__(self, rhs):
        return self.bin_expr(BinExprType.Xor, rhs)
    
    def __lshift__(self, rhs):
        return self.bin_expr(BinExprType.Sll, rhs)
    
    def __rshift__(self, rhs):
        return self.bin_expr(BinExprType.Srl, rhs)
    
    def __neg__(self):
        return self.bin_expr(BinExprType.Not, rhs)
   
    def __invert__(self): 
        self.to_expr()
        lhs = pop_expr()
        return expr(ExprUnaryModel(UnaryExprType.Not, lhs))
    
    def inside(self, rhs):
        self.to_expr()
        lhs_e = pop_expr()
        
        if isinstance(rhs, rangelist):
            return expr(ExprInModel(lhs_e, rhs.range_l))
        elif isinstance(rhs, rng):
            rl = ExprRangelistModel()
            rl.add_range(ExprRangeModel(rhs.low, rhs.high))
            return expr(ExprInModel(lhs_e, rl))
        elif isinstance(rhs, list_t):
            return expr(ExprInModel(
                lhs_e,
                ExprRangelistModel(
                    [ExprFieldRefModel(rhs.get_model())])))
        else:
            raise Exception("Unsupported 'inside' argument of type " + str(type(rhs)))

    def outside(self, rhs):
        self.not_inside(rhs)
            
    def not_inside(self, rhs):
        self.to_expr()
        lhs_e = pop_expr()
        
        if isinstance(rhs, rangelist):
            return expr(ExprUnaryModel(
                UnaryExprType.Not,
                ExprInModel(lhs_e, rhs.range_l)))
        elif isinstance(rhs, list_t):
            return expr(ExprUnaryModel(
                UnaryExprType.Not,
                ExprInModel(lhs_e,
                    ExprRangelistModel(
                        [ExprFieldRefModel(rhs.get_model())]))))
        else:
            raise Exception("Unsupported 'not_inside' argument of type " + str(type(rhs)) + " expect rangelist or list_t")
        
    
        
    def __getitem__(self, rng):
        if is_expr_mode():
            if isinstance(rng, slice):
                # slice
                to_expr(rng.start)
                upper = pop_expr()
                to_expr(rng.stop)
                lower = pop_expr()
                return expr(ExprPartselectModel(
                    ExprFieldRefModel(self._int_field_info.model), upper, lower))
            else:
                # single value
                to_expr(rng)
                e = pop_expr()
                return expr(ExprPartselectModel(
                    ExprFieldRefModel(self._int_field_info.model), e))
        else:
            curr = int(self.get_model().get_val())
            if isinstance(rng, slice):
                msk = ((1 << (rng.start-rng.stop+1))-1) << rng.stop
                curr = (curr & msk) >> rng.stop
            else:
                curr = (curr & (1 << rng)) >> rng
            return curr
            
    def __setitem__(self, rng, val):
        if not is_expr_mode():
            curr = int(self.get_model().get_val())
            if isinstance(rng, slice):
                msk = ((1 << (rng.start-rng.stop))-1) << rng.stop
                curr = (curr & msk) | (val << rng.stop & msk)
            else:
                curr = (curr & ~(val << rng)) | (val << rng)
            self.get_model().set_val(curr)
        else:
            raise Exception("Cannot assign to a part-select within a constraint")
        
    def clone(self):
        return type_base(self.width, self.is_signed)

class type_bool(type_base):
    """Base class for boolean fields"""
    
    def __init__(self, i=False):
        super().__init__(1, False, 1 if i else 0)
        
    def build_field_model(self, name):
        # If we have an IntEnum, then collect the values
        self._int_field_info.name = name
        self._int_field_info.model = EnumFieldModel(
            name,
            self.enum_i.enums,
            self._int_field_info.is_rand
        )
        return self._int_field_info.model        
        
    def get_val(self):
        """Gets the field value"""
        return bool(self.get_model().get_val())
    
    def set_val(self, val):
        """Sets the field value"""
        self.get_model().set_val(bool(val))

class type_enum(type_base):
    """Base class for enumerated-type fields"""
    
    def __init__(self, t, i=None):
        # TODO: determine size of enum
        self.enum_i = EnumInfo.get(t)

        width = 32
        is_signed = True
        
        super().__init__(width, is_signed, i)

        # The value of an enum field is stored in two ways
        # The enum_id is the index into the enum type
        # The 'val' field is the actual enum value        
        self.enum_id = 0
        if i is not None:
            # TODO
#            self.enum_id = list(t).f
            pass
        
    def build_field_model(self, name):
        # If we have an IntEnum, then collect the values
                
        self._int_field_info.name = name
        self._int_field_info.model = EnumFieldModel(
            name,
            self.enum_i.enums,
            self._int_field_info.is_rand
        )
        return self._int_field_info.model        
        
    def get_val(self):
        """Returns the enum id"""
        val = int(self.get_model().get_val())
        return self.enum_i.v2e(val)
    
    def set_val(self, val):
        """Sets the enum id"""
        self.get_model().set_val(self.enum_i.e2v(val))
    
class enum_t(type_enum):
    """Creates a non-random enumerated-type attribute"""
    
    def __init__(self, t, i=None):
        super().__init__(t, i)
        
class rand_enum_t(enum_t):
    """Creates a random enumerated-type attribute"""
    
    def __init__(self, t, i=None):
        super().__init__(t, i)
        self._int_field_info.is_rand = True
        
class bit_t(type_base):
    """Creates an unsigned arbitrary-width attribute"""
    def __init__(self, w=1, i=0):
        super().__init__(w, False, i)
        
class bool_t(type_base):
    """Creates a boolean field"""
    def __init__(self, i=False):
        super().__init__(1, False, 1 if i else 0)

class uint8_t(bit_t):
    """Creates an unsigned 8-bit attribute"""
    def __init__(self, i=0):
        super().__init__(8, i)
        
class uint16_t(bit_t):
    """Creates an unsigned 16-bit attribute"""
    def __init__(self, i=0):
        super().__init__(16, i)
        
class uint32_t(bit_t):
    """Creates an unsigned 32-bit attribute"""
    def __init__(self, i=0):
        super().__init__(32, i)
        
class uint64_t(bit_t):
    """Creates an unsigned 64-bit attribute"""
    def __init__(self, i=0):
        super().__init__(64, i)

class rand_bit_t(bit_t):
    """Creates a random unsigned arbitrary-width attribute"""
    
    def __init__(self, w=1, i=0):
        super().__init__(w, i)
        self._int_field_info.is_rand = True
        
class rand_uint8_t(rand_bit_t):
    """Creates a random unsigned 8-bit attribute"""
    def __init__(self, i=0):
        super().__init__(8, i)
        
class rand_uint16_t(rand_bit_t):
    """Creates a random unsigned 16-bit attribute"""
    def __init__(self, i=0):
        super().__init__(16, i)
        
class rand_uint32_t(rand_bit_t):
    """Creates a random unsigned 32-bit attribute"""
    def __init__(self, i=0):
        super().__init__(32, i)
        
class rand_uint64_t(rand_bit_t):
    """Creates a random unsigned 64-bit attribute"""
    def __init__(self, i=0):
        super().__init__(64, i)
        
class int_t(type_base):
    """Creates a signed arbitrary-width attribute"""
    
    def __init__(self, w=32, i=0):
        super().__init__(w, True, i)
        
class int8_t(int_t):
    """Creates a signed 8-bit attribute"""
    def __init__(self, i=0):
        super().__init__(8, i)
        
class int16_t(int_t):
    """Creates a signed 16-bit attribute"""
    def __init__(self, i=0):
        super().__init__(16, i)
        
class int32_t(int_t):
    """Creates a signed 32-bit attribute"""
    def __init__(self, i=0):
        super().__init__(32, i)
        
class int64_t(int_t):
    """Creates a signed 64-bit attribute"""
    def __init__(self, i=0):
        super().__init__(64, i)
        
class rand_int_t(int_t):
    """Creates a random signed arbitrary-width attribute"""
    
    def __init__(self, w=32, i=0):
        super().__init__(w, i)
        self._int_field_info.is_rand = True

class rand_int8_t(rand_int_t):
    """Creates a random signed 8-bit attribute"""
    def __init__(self, i=0):
        super().__init__(8, i)
        
class rand_int16_t(rand_int_t):
    """Creates a random signed 16-bit attribute"""
    def __init__(self, i=0):
        super().__init__(16, i)
        
class rand_int32_t(rand_int_t):
    """Creates a random signed 32-bit attribute"""
    def __init__(self, i=0):
        super().__init__(32, i)
        
class rand_int64_t(rand_int_t):
    """Creates a random signed 64-bit attribute"""
    def __init__(self, i=0):
        super().__init__(64, i)        
        
class list_t(object):
    
    def __init__(self, 
                 t, 
                 sz=0, 
                 is_rand=False, 
                 is_randsz=False,
                 init=None):
        self.t = t
        self._int_field_info = field_info()
        self.is_scalar = isinstance(t, (type_base,type_enum))
        if self.is_scalar:
            self.mask = (1 << self.t.width)-1
        self.is_enum = isinstance(t, type_enum)
        self._int_field_info.is_rand = is_rand
        self.is_rand_sz = is_randsz
        self.init_sz = sz
        self.init = init
        
        if self.init is not None and self.init_sz > 0:
            raise Exception("Only one of 'init' and 'sz' may be specified")
        
        if not self.is_scalar:
            if not hasattr(t, "_int_field_info"):
                raise Exception("list_t type " + str(t) + " (type " + str(type(t)) + ") is not a VSC randobj type")
            
            # Fill out field index and parent relationships
            # to support indexed field access
            # TODO: look out for recursive relationships...
            with expr_mode():
                self._id_fields(t, None)
            
        # Non-scalar arrays require a backing array
        self.backing_arr = []
        
    def _id_fields(self, it, parent):
        """Apply an ID to all fields, so they can be referenced in 
        foreach constraints
        """
        it._int_field_info.parent = parent

        fid = 0        
        for fn in dir(it):
            fo = getattr(it, fn)
            if hasattr(fo, "_int_field_info"):
                fi = fo._int_field_info
                fi.id = fid
                fi.parent = it._int_field_info
                fid += 1
                
                if fi.is_composite:
                    self._id_fields(fo, fi)
        
    def get_model(self):
        if self._int_field_info.model is None:
            enums = None if not self.is_enum else self.t.enum_i.enums
            type_t = self.t.get_model()
            # Save the user-visible (Python) name for later use
            if hasattr(self.t, "name"):
                type_t.name = self.t.tname
            else:
                type_t.name = "<primitive>"
            self._int_field_info.model = FieldArrayModel(
                "<unknown-array>",
                type_t,
                self.is_scalar,
                enums,
                self.t.width if self.is_scalar else -1,
                self.t.is_signed if self.is_scalar else -1,
                self._int_field_info.is_rand,
                self.is_rand_sz)
           
            if self.init_sz > 0:
                if self.is_enum:
                    ei : EnumInfo = self.t.enum_i
                    ev = ei.v2e_m[ei.enums[0]]
                    for i in range(self.init_sz):
                        self.append(ev)
                elif self.is_scalar:
                    for i in range(self.init_sz):
                        self.append(0)
                else:
                    for i in range(self.init_sz):
                        self.append(type(self.t)())
            elif self.init is not None:
                self.extend(self.init)
            
        return self._int_field_info.model

    def build_field_model(self, name):
        model = self.get_model()
        model.name = name
        self._int_field_info.name = name
        
        return model

    @property    
    def size(self):
        model = self.get_model()
        if get_expr_mode():
            return expr(ExprFieldRefModel(model.size))
        else:
            return int(model.size.get_val())
        
    @property
    def sum(self):
        if self.is_scalar:
            if get_expr_mode():
                return expr(ExprArraySumModel(self.get_model()))
            else:
                ret = 0
                for f in self.get_model().field_l:
                    ret += int(f.get_val())
                return ret
        else:
            raise Exception("Composite arrays do not have a sum")

    @property
    def product(self):
        if self.is_scalar:
            if get_expr_mode():
                return expr(ExprArrayProductModel(self.get_model()))
            else:
                ret = 0 if self.size == 0 else 1
                for f in self.get_model().field_l:
                    ret *= int(f.get_val())
                return ret
        else:
            raise Exception("Composite arrays do not have a product")
            
        
    def __len__(self):
        if get_expr_mode():
            raise Exception("len cannot be used in constraints")
        else:
            return self.size
        
    def append(self, v):
        model = self.get_model()
        
        if self.is_enum:
            ei : EnumInfo = self.t.enum_i
            enum_m = EnumFieldModel(
                "xxx",
                ei.enums,
                self._int_field_info.is_rand)
            enum_m.set_val(ei.e2v(v))
            model.append(enum_m)
        elif self.is_scalar:
            # Working with a scalar
            f = model.add_field()
            mask_v = int(v) & self.mask
            f.set_val(mask_v)
        else:
            if not issubclass(type(v), type(self.t)):
                raise Exception("Attempting to append illegal element to object array")
            self.backing_arr.append(v)
            model.append(v.get_model())
            # Propagate randomization information
            v.get_model().is_declared_rand = self.get_model().is_declared_rand
            
    def extend(self, v):
        for vi in v:
            self.append(vi)
        
    def clear(self):
        self.get_model().clear()

    def __contains__(self, lhs):
        if get_expr_mode():
            to_expr(lhs)
            return expr(ExprInModel(
                pop_expr(), 
                ExprRangelistModel(
                    [ExprFieldRefModel(self.get_model())])))
        else:
            model = self.get_model()
            if self.is_enum:
                ei : EnumInfo = self.t.enum_i
                val = ei.e2v(lhs)
                for f in model.field_l:
                    if int(f.get_val()) == val:
                        return True
            elif self.is_scalar:
                for f in model.field_l:
                    if int(f.get_val()) == int(lhs):
                        return True
            else:
                return lhs in self.backing_arr
            return False

    def __iter__(self):
        class list_scalar_it(object):
            def __init__(self, l):
                self.l = l
                self.model = l._int_field_info.model
                self.idx = 0
                
            def __next__(self):
                if self.idx >= int(self.model.size.get_val()):
                    raise StopIteration()
                else:
                    # The model's view is always masked 2's complement
                    v = int(self.model.field_l[self.idx].get_val())
                    
                    if self.l.t.is_signed:
                        if (v & (1 << (self.l.t.width-1))) != 0:
                            v = -((~v & self.l.mask)+1)
                        
                    self.idx += 1
                    return int(v)
        class list_object_it(object):
            def __init__(self, l):
                self.l = l
                self.model = l._int_field_info.model
                self.idx = 0
                
            def __next__(self):
                if self.idx >= int(self.model.size.get_val()):
                    raise StopIteration()
                else:
                    v = self.l.backing_arr[self.idx]
                    self.idx += 1
                    return v
                
        if self.is_scalar:
            return list_scalar_it(self)
        else:
            return list_object_it(self)
    
    def __getitem__(self, k):
        model = self._int_field_info.model
        if get_expr_mode():
            # TODO: must determine whether we're within a foreach or just on our own
            to_expr(k)
            idx_e = pop_expr()
                 
            return expr_subscript(ExprArraySubscriptModel(
                ExprFieldRefModel(self.get_model()),
                idx_e))
            
#             if is_foreach_arr(self):
#                 to_expr(k)
#                 idx_e = pop_expr()
#                 
#                 return expr_subscript(ExprArraySubscriptModel(
#                     ExprFieldRefModel(self.get_model()),
#                     idx_e))
#             else:
#                 to_expr(k)
#                 idx_e = pop_expr()
#                 return expr_subscript(ExprArraySubscriptModel(
#                     ExprFieldRefModel(self.get_model()),
#                     idx_e))
        else:
            if self.is_enum:
                ei : EnumInfo = self.t.enum_i
                return ei.v2e(model.field_l[k].get_val())
            elif self.is_scalar:
                # The model's view is always masked 2's complement
                v = int(model.field_l[k].get_val())
                
                if self.t.is_signed:
                    if (v & (1 << (self.t.width-1))) != 0:
                        v = -((~v & self.mask)+1)
                        
                return v
            else:
                return self.backing_arr[k]
            
    def __setitem__(self, k, v):
        if self.is_enum:
            ei : EnumInfo = self.t.enum_i
            val = ei.e2v(v)
            self.get_model().field_l[k].set_val(val)
        elif self.is_scalar:
            self.get_model().field_l[k].set_val(
                ValueScalar(int(v) & (1 << self.t.width)-1))
        else:
            self.backing_arr[k] = v
            
    def __str__(self):
        ret = "["
        if self.is_enum:
            ei : EnumInfo = self.t.enum_i
            model = self._int_field_info.model
            for i in range(self.size):
                if i > 0:
                    ret += ", "
                ret += str(ei.v2e(model.field_l[i].get_val()))
        elif self.is_scalar:
            model = self._int_field_info.model
            for i in range(self.size):
                if i > 0:
                    ret += ", "
                ret += model.field_l[i].get_val().toString()
        else:
            for i in range(self.size):
                if i > 0:
                    ret += ", "
                ret += str(self.backing_arr[i])
        
        ret += "]"
        
        return ret

    def to_expr(self):
        return expr(ExprFieldRefModel(self.get_model()))

    
class rand_list_t(list_t):
    """List of random elements with a non-random size"""
    
    def __init__(self, t, sz=0):
        super().__init__(t, sz, is_rand=True)
        
class randsz_list_t(list_t):
    """List of random elements with a non-random size"""
    
    def __init__(self, t):
        super().__init__(t, is_rand=True, is_randsz=True)
        

