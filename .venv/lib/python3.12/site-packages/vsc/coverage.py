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

# Created on Aug 3, 2019
#
# @author: ballance

from enum import Enum, auto
import enum
import inspect

from vsc.impl import ctor
from vsc.impl.coverage_registry import CoverageRegistry
from vsc.impl.covergroup_int import CovergroupInt
from vsc.impl.ctor import pop_expr
from vsc.impl.expr_mode import expr_mode
from vsc.impl.options import Options
from vsc.impl.type_options import TypeOptions
from vsc.model.covergroup_model import CovergroupModel
from vsc.model.coverpoint_bin_array_model import CoverpointBinArrayModel
from vsc.model.coverpoint_bin_collection_model import CoverpointBinCollectionModel
from vsc.model.coverpoint_bin_enum_model import CoverpointBinEnumModel
from vsc.model.coverpoint_bin_single_bag_model import CoverpointBinSingleBagModel
from vsc.model.coverpoint_bin_single_val_model import CoverpointBinSingleValModel
from vsc.model.coverpoint_cross_model import CoverpointCrossModel
from vsc.model.coverpoint_model import CoverpointModel
from vsc.model.enum_field_model import EnumFieldModel
from vsc.model.expr_fieldref_model import ExprFieldRefModel
from vsc.model.expr_ref_model import ExprRefModel
from vsc.model.field_composite_model import FieldCompositeModel
from vsc.model.field_scalar_model import FieldScalarModel
from vsc.model.rangelist_model import RangelistModel
from vsc.model.source_info import SourceInfo
from vsc.types import rangelist, bit_t, to_expr, type_base, enum_t, type_enum, \
    expr, field_info
from vsc.impl.wildcard_bin_factory import WildcardBinFactory
from vsc.model.coverpoint_bin_single_wildcard_model import CoverpointBinSingleWildcardModel
from vsc.model.wildcard_binspec import WildcardBinspec


def covergroup(T):
    """Covergroup decorator marks as class as being a covergroup"""
    
    if not hasattr(T, "_cg_init"):
        def dump(self, ind=""):
            model = self.get_model()
            model.dump(ind)
            
        # TODO: Make adding sample parameters additive?
        def with_sample(self, *args, **kwargs):
            model = self.get_model()
            cg_i = self._get_int()
            if len(args) == 1 and isinstance(args[0], dict):
                params = args[0]
            elif len(kwargs) > 0:
                params = kwargs
            else:
                raise Exception("incorrect call to with_sample. Expect single dict parameter or kwargs")
                
            for pn,pt in params.items():
                if hasattr(pt, "_int_field_info"):
                    pm = pt.build_field_model(pn)
                    pt._int_field_info.name = pn
                    # Note: this is only used if the field is a list
                    pt._int_field_info.id = len(model.field_l)
                    if hasattr(pt, "_id_fields"):
                        # This field is a composite field, and we
                        # must access its children via indexed references
                        pt._id_fields(
                            pt,
                            self._int_field_info)
                    else:
                        # Scalar field
                        pt._int_field_info.parent = self._int_field_info
                    setattr(self, pn, pt)
                    cg_i.sample_var_l.append(pn)
                    cg_i.sample_obj_l.append(pt)
            
                    # Add a field to the covergroup model
                    model.add_field(pm)
                    
                    pt._int_field_info.root_e = ExprFieldRefModel(model)
                else:
                    raise Exception("Sample arguments must vsc objects, not " + str(pt))
#             elif len(kwargs) > 0:
#                 for pn,pt in kwargs.items():
#                     if hasattr(pt, "build_field_model"):
#                         setattr(self, pn, pt)
#                         pm = pt.build_field_model(pn)
#                         # Add a field to the covergroup model
#                         model.add_field(pm)
#                         cg_i.sample_var_l.append(pn)
#                         cg_i.sample_obj_l.append(pt)
#                     else:
#                         print("TODO: handle non-field-model")
#                         setattr(self, pn, lambda:getattr(self, "_" + pn))
#            else:
#                raise Exception("incorrect call to with_sample")
                
        def sample(self, *args, **kwargs):
            """Base sampling method that samples all coverpoints and crosses"""
            # Build the model if we haven't yet
            cg_i = self._get_int()
            
            # TODO: Need to propagate values to base classes
            model = self.get_model()
            
            sample_var_len = len(cg_i.sample_var_l)
            
            if len(args) != sample_var_len:
                raise Exception("Wrong number of parameters: expect " + str(sample_var_len) + " receive " + str(len(args)))

            model = self.get_model()        
            for i in range(len(args)):
                # TODO: need to account for inheritance
                ex_f = model.get_field(i)
                us_f = cg_i.sample_obj_l[i]
                if isinstance(ex_f, FieldCompositeModel):
                    # TODO: probably need to do something a bit more than this?
                    model.set_field(i, args[i].get_model())
                elif isinstance(ex_f, EnumFieldModel):
                    ei = us_f.enum_i
                    if isinstance(args[i], type_enum):
                        ex_f.set_val(args[i].get_val())
                    else:
                        # Use the enum map to convert to an int
                        ex_f.set_val(ei.e2v(args[i]))
                elif isinstance(ex_f, FieldScalarModel):
                    if isinstance(args[i], type_base):
                        ex_f.set_val(args[i].get_val())
                    else:
                        ex_f.set_val(int(args[i]))
                else:
                    raise Exception("unhandled sample case")
                        
                    
                setattr(self, cg_i.sample_var_l[i], args[i])
#                getattr(self, cg_i.sample_var_l[i]).set_val(args[i])

            model.sample()

        pass
        
        def get_coverage(self):
            return self.get_model().get_coverage()
        
        def get_inst_coverage(self):
            return self.get_model().get_inst_coverage()
        
        def get_model(self):
            cg_i = self._get_int()
            
            if cg_i.model is None:
                cg_i.model = CovergroupModel(T.__name__)
                cg_i.model.srcinfo_decl = getattr(type(self), "_srcinfo_decl")
                cg_i.model.srcinfo_inst = cg_i.srcinfo_inst
            
            return cg_i.model
        
        def build_model(self):
            cg_i = self._get_int()
            self.get_model()

            cg_i.model.options = self.options.create_model(None)
            
            # Configure the covergroup name
            # - name specified via 'set_name' takes precedence
            # - name specified via option has second level
            
            name = T.__name__
            if hasattr(self, "name") and self.name is not None:
                name = self.name
            elif self.options.name is not None:
                name = self.options.name
                
            cg_i.model.name = name
            
            obj_name_m = {}
            for n in dir(self):
                obj = getattr(self, n)
                if hasattr(obj, "build_cov_model"):
                    obj_name_m[obj] = n
                    
            for b in self.buildable_l:
                cp_m = b.build_cov_model(cg_i.model, obj_name_m[b])
                cg_i.model.add_coverpoint(cp_m)
                
            # Register the covergroup in the registry. This will ensure that
            # this coverage instance is properly connected to the type coverage
            # If the instance covergroup happens to be parameterized,
            # then the type covergroup must have the same parameterization
            CoverageRegistry.inst().register_cg(self.get_model())
            
                
            # We're done, so lock the covergroup
            self.lock()

            # Finalize the contents of the covergroup                
            cg_i.model.finalize()
        
        def _get_int(self):
            if not hasattr(self, "_cg_int"):
                self._cg_int = CovergroupInt(self)
            return self._cg_int
        
        def lock(self):
            cg_i = self._get_int()
            cg_i.locked = True
            self.options.lock()
            self.type_options._lock()
        
        def _setattr(self, field, val):
            if hasattr(val, "build_cov_model"):
                if not hasattr(self, "buildable_l"):
                    object.__setattr__(self, "buildable_l", [])
                self.buildable_l.append(val)
            object.__setattr__(self, field, val)
            
        def set_name(self, name):
            self.name = name
           
            cg_i = self._get_int()
            if cg_i.model is not None:
                cg_i.model.name = name
                
        def get_name(self) -> str:
            return self.name
            
        def configure_options(self, *args, **kwargs):
            if len(args) == 1 and isinstance(args[0], dict):
                opts=args[0]
            else:
                opts = kwargs

            print("TODO: reconfigure options")
            print("TODO: detect wether options are locked")
            
            return self
        
        setattr(T, "dump", dump)
        setattr(T, "with_sample", with_sample)
        setattr(T, "sample", sample)
        setattr(T, "get_coverage", get_coverage)
        setattr(T, "get_inst_coverage", get_inst_coverage)
        setattr(T, "get_model", get_model)
        setattr(T, "build_model", build_model)
        setattr(T, "_get_int", _get_int)
        setattr(T, "lock", lock)
        setattr(T, "__setattr__", _setattr)
        setattr(T, "set_name", set_name)
        setattr(T, "get_name", get_name)
        setattr(T, "_cg_init", True)
        setattr(T, "configure_options", configure_options)
    else:
        raise Exception("Covergroup inheritance is not currently supported")
        
    # Store declaration information on the type
    if hasattr(T, "__file__"):
        file = inspect.getsourcefile(T)
        lineno = inspect.getsourcelines(T)[1]
    else:
        file = "<unknown>"
        lineno = -1
    setattr(T, "_srcinfo_decl", SourceInfo(file, lineno))

    # This is the interposer class that wraps a user-defined
    # covergroup class. It ensures that the coverage model is
    # created while field refs are treated as expressions
    class covergroup_interposer(T):
        
        def __init__(self, *args, **kwargs):
            cg_i = self._get_int()

            # Capture the instantiation location of this covergroup            
            frame = inspect.stack()[1]
            cg_i.srcinfo_inst = SourceInfo(frame.filename, frame.lineno)

            self.buildable_l = []
            
            # Construct the model            
            model = self.get_model()
            
            # Ensure options/type_options created before 
            # calling (user) base-class __init__
            if not hasattr(self, "options"):
                self.options = Options()
            if not hasattr(self, "type_options"):
                self.type_options = TypeOptions()
                
            for a in args:
                if hasattr(a, "_ro_init"):
                    # Ensure the model is constructed
                    a.get_model()
                    
            if cg_i.ctor_level == 0:
                self._int_field_info = field_info()
                self._int_field_info.root_e = ExprFieldRefModel(model)

            with cg_i:                
                super().__init__(*args, **kwargs)

            if cg_i.ctor_level == 0:
                # TODO: need to actually elaborate the model
                self.build_model()
                
    ret = type(T.__name__, (covergroup_interposer,), dict())
    
    return ret

        
class bin(object):
    """Specifies a single coverage bin"""
    def __init__(self, *args):
        self.range_l = args
        
        # Capture the declaration location of this bin
        frame = inspect.stack()[1]
        self.srcinfo_decl = SourceInfo(frame.filename, frame.lineno)
        
    def build_cov_model(self, parent, name, exclude_bins : RangelistModel):
        # Construct a range model
        range_l = RangelistModel(self.range_l)
        range_l.compact()
        
        if exclude_bins is not None and len(exclude_bins.range_l) > 0:
            # Apply exclusions
            range_l.intersect(exclude_bins)
            
        ret = CoverpointBinSingleBagModel(name, range_l)
        ret.srcinfo_decl = self.srcinfo_decl
        
        return ret
        

class bin_array(object):
    """Specifies an array of bins"""
    
    def __init__(self, nbins, *args):
        """
        args may be one of two formats
        - Single list of tuples or lists of values or ranges (eg [[1], [2,4], [8]])
        - Arguments comprising values and ranges (eg 1, [2,4], 8)
        """
        self.nbins = nbins
        self.ranges = RangelistModel()
        
        # Convert the specification into canonical form: list of tuples
        if len(args) == 1:
            # Argument must be a value, a single-level list, or 
            if isinstance(args[0], (list,tuple)):
                # Must determine whether this is a programmatic description
                # or a single user-specified range
                if isinstance(args[0][0], (list,tuple)):
                    # Programmatic description
                    for r in args:
                        if isinstance(r, (list,tuple)):
                            if len(r) not in [1,2]:
                                raise Exception("Programmatic bin specification elements require 1 or 2 elements: " + str(r))
                            self.ranges.add_range(r[0], r[1])
                        elif isinstance(r, int):
                            self.ranges.add_value(r)
                        else:
                            raise Exception("Unknown bin specification " + str(r))
                else:
                    # User-specified range
                    if len(args[0]) != 2:
                        raise Exception("Expect two elements in a user-specified range")
                    if not isinstance(args[0][0], int):
                        raise Exception("Bin value " + str(args[0][0]) + " is not integral")
                    if not isinstance(args[0][1], int):
                        raise Exception("Bin value " + str(args[0][1]) + " is not integral")
                    self.ranges.add_range(args[0][0], args[0][1])
            elif isinstance(args[0],int):
                # user-specified single-value bin
                self.ranges.add_value(args[0])
            else:
                raise Exception("Bin specification " + str(args[0]) + " is neither value nor range")
            pass
        else:
            # Multiple arguments. Expect each to be a single-level tuple or list
            for a in args:
                if isinstance(a,(list,tuple)):
                    if len(a) != 2:
                        raise Exception("Bin range " + str(a) + " must have two elements")
                    else:
                        self.ranges.add_range(a[0], a[1])
                elif isinstance(a,int):
                    self.ranges.add_value(a)
                else:
                    raise Exception("Bin specification " + str(a) + " is neither value nor range")

        if isinstance(nbins,list):
            if len(nbins) not in (0,1):
                raise Exception("Only 0 or 1 argument can be specified to the nbins argument")
            self.nbins = -1 if len(nbins) == 0 else nbins[0]
        else:
            self.nbins = int(nbins)
        
        if len(args) == 0:
            raise Exception("No bins range specified")
        
        self.ranges.compact()
        
        # Capture the declaration location of this bin
        frame = inspect.stack()[1]
        self.srcinfo_decl = SourceInfo(frame.filename, frame.lineno)
    
    def build_cov_model(self, parent, name, exclude_bins : RangelistModel):
        ret = None

        if len(exclude_bins.range_l) > 0:
            self.ranges.intersect(exclude_bins)
        
        # First, need to determine how many total bins
        # Construct a range model
        if self.nbins == -1:
            # unlimited number of bins
            if len(self.ranges.range_l) == 1:
                r = self.ranges.range_l[0]
                ret = CoverpointBinArrayModel(name, r[0], r[1])
            else:
                idx=0
                ret = CoverpointBinCollectionModel(name)
                for r in self.ranges.range_l:
                    if r[0] != r[1]:
                        b = ret.add_bin(CoverpointBinArrayModel(name, r[0], r[1]))
                        b.srcinfo_decl = self.srcinfo_decl
                        idx += ((r[1] - r[0]) + 1)
                    elif r[0] == r[1]:
                        b = ret.add_bin(CoverpointBinSingleValModel(name + "[" + str(idx) + "]", r[0]))
                        b.srcinfo_decl = self.srcinfo_decl
                        idx += 1
                    else:
                        raise Exception("Internal error: expect bin to have 1 or 2 elements not " + 
                                        str(len(r)) + " (" +
                                        name + " " + self.srcinfo_decl.filename + ":" +
                                        str(self.srcinfo_decl.lineno) + ")")
        else:
            ret = CoverpointBinCollectionModel.mk_collection(name, 
                    self.ranges, self.nbins)
        
        ret.srcinfo_decl = self.srcinfo_decl

        return ret
    
class wildcard_bin(object):
    """Specifies a single wildcard coverage bin"""
    def __init__(self, *args):
        # Capture the declaration location of this bin
        self.srcinfo_decl = SourceInfo.mk()

        self.range_l = []
        for a in args:
            if isinstance(a, tuple):
                # Expressed in mask form
                # (value, mask) where 1-bits in mask are compared and 0-bits are ignored
                self.range_l.append(a)
            elif isinstance(a, str):
                # Expressed in string form in either oct, hex, or bin format
                # 
                value, mask = WildcardBinFactory.str2bin(a)
                self.range_l.append((value,mask))
            else:
                raise Exception("Unknown argument %s to wildcard bin. Expect tuple or string" % (
                    str(a)))
        
    def build_cov_model(self, parent, name, excluded_bins):
        ret = CoverpointBinSingleWildcardModel(
            name, 
            WildcardBinspec(self.range_l))
        ret.srcinfo_decl = self.srcinfo_decl
        
        return ret    

class wildcard_bin_array(object):
    """Specifies an array of bins using wildcard specifications"""
    
    def __init__(self, nbins, *args):
        """
        args may be one of two formats
        - Single list of wildcard strings (eg "0x82x")
        - Single list of value/mask tuples (eg [(0x820,0xFF0)])
        - Single string
        - Single tuple
        """
        self.nbins = nbins
        self.range_l = []
        
        # Convert the specification into canonical form: list of tuples
        if len(args) == 1:
            if isinstance(args[0], str):
                value, mask = WildcardBinFactory.str2bin(args[0])
                self.range_l.extend(WildcardBinFactory.valmask2binlist(value, mask))
            elif isinstance(args[0], (list,tuple)):
                # value/mask
                if len(args[0]) != 2:
                    raise Exception("Wildcard bin specification requires two elements (value,mask)")
                
                self.range_l.extend(WildcardBinFactory.valmask2binlist(args[0][0], args[0][1]))
            else:
                raise Exception("Bin specification " + str(args[0]) + " is neither string nor value/mask")
            pass
        else:
            # Multiple arguments. Expect each to be a single-level string or tuple
            for a in args:
                if isinstance(a,(list,tuple)):
                    if len(a) != 2:
                        raise Exception("Wildcard bin range " + str(a) + " must have two elements")
                    else:
                        self.range_l.extend(WildcardBinFactory.valmask2binlist(a[0], a[1]))
                elif isinstance(a,str):
                    value, mask = WildcardBinFactory.str2bin(a)
                    self.range_l.extend(WildcardBinFactory.valmask2binlist(value, mask))
                else:
                    raise Exception("Wildcard bin specification " + str(a) + " is neither value nor range")
                
        # TODO: handle overlap
        self.range_l.sort(key=lambda e: e[0])
        
        # Now, collapse overlaps
        i=0
        while i < len(self.range_l):
            if i+1 < len(self.range_l) and self.range_l[i][1]+1 >= self.range_l[i+1][0]:
                self.range_l[i] = (self.range_l[i][0], self.range_l[i+1][1])
                self.range_l.pop(i+1)
            else:
                i += 1

        if isinstance(nbins,list):
            if len(nbins) not in (0,1):
                raise Exception("Only 0 or 1 argument can be specified to the nbins argument")
            self.nbins = -1 if len(nbins) == 0 else nbins[0]
        else:
            self.nbins = int(nbins)
        
        if len(args) == 0:
            raise Exception("No bins range specified")
        
        # Capture the declaration location of this bin
        frame = inspect.stack()[1]
        self.srcinfo_decl = SourceInfo(frame.filename, frame.lineno)
    
    def build_cov_model(self, parent, name, excluded_bins):
        ret = None
        
        # First, need to determine how many total bins
        # Construct a range model
        if self.nbins == -1:
            # unlimited number of bins
            if len(self.range_l) == 1:
                r = self.range_l[0]
                ret = CoverpointBinArrayModel(name, r[0], r[1])
            else:
                idx=0
                ret = CoverpointBinCollectionModel(name)
                for r in self.range_l:
                    if len(r) == 2:
                        if r[0] != r[1]:
                            b = ret.add_bin(CoverpointBinArrayModel(name, r[0], r[1]))
                            b.srcinfo_decl = self.srcinfo_decl
                            idx += ((r[1] - r[0]) + 1)
                        else:
                            b = ret.add_bin(CoverpointBinSingleValModel(name + "[" + str(idx) + "]", r[0]))
                            b.srcinfo_decl = self.srcinfo_decl
                            idx += 1
                    elif len(r) == 1:
                        b = ret.add_bin(CoverpointBinSingleValModel(name + "[" + str(idx) + "]", r[0]))
                        b.srcinfo_decl = self.srcinfo_decl
                        idx += 1
                    else:
                        raise Exception("Internal error: expect bin to have 1 or 2 elements not " + 
                                        str(len(r)) + " (" +
                                        name + " " + self.srcinfo_decl.filename + ":" +
                                        str(self.srcinfo_decl.lineno) + ")")
        else:
            ret = CoverpointBinCollectionModel.mk_collection(name, 
                    RangelistModel(self.range_l), self.nbins)
        
        ret.srcinfo_decl = self.srcinfo_decl

        return ret
        
class binsof(object):
    # TODO: future implementation of the 'binsof' operator
    
    def __init__(self, cp):
        pass
    

    def intersect(self, rng):
        pass

    def __and__(self, rhs):
        pass
    
    def __not__(self, rhs):
        pass
    
    def __or__(self, rhs):
        pass
    
class coverpoint(object):
   
    def __init__(self, 
            target, 
            cp_t=None,  # Type of the coverpoint, when it needs to be specified
            iff=None, 
            bins=None, 
            ignore_bins=None,
            illegal_bins=None,
            options=None, 
            type_options=None,
            name=None):
        self.have_var = False
        self.target = None
        self.cp_t = cp_t
        self.model = None
        self.target_kind = None
        self.target_type = None
        self.get_val_f = None
        self.options = Options()
        self.type_options = TypeOptions()
        self.name = name
        self.iff = None
        self.iff_f = None
        
        # Capture the declaration location of this coverpoint
        frame = inspect.stack()[1]
        self.srcinfo_decl = SourceInfo(frame.filename, frame.lineno)
        
        ctor.clear_exprs()
        
        if options is not None:
            self.options.set(options)
            
        if type_options is not None:
            self.type_options.set(type_options)

        with expr_mode():
            if isinstance(target, type_enum):
                self.have_var = True
                self.target = target.to_expr().em
                self.cp_t = target
            elif isinstance(target, type_base):
                self.have_var = True
                self.target = target.to_expr().em
                self.cp_t = target
            elif callable(target):
                if cp_t is None and bins is None:
                    raise Exception("Auto-binned coverpoint with a callable target must specify type using 'cp_t'")

                # Accept the user-specified type
                self.cp_t = cp_t
            
                self.target = target
                self.get_val_f = target
            elif isinstance(target, expr):
                self.have_var = True
                self.target = target.em
                if cp_t is not None:
                    self.cp_t = cp_t
                else:
                    # Get the express width for the implied type
                    self.cp_t = bit_t(target.em.width())
            else:
                # should be an actual variable (?)
                # TODO: or, could be an expression
                print("TODO: handle actual variables")
                to_expr(target)
                self.target = pop_expr()
                print("target=" + str(self.target))
                self.get_val_f = self.target.val
                print("self.get_val_f=" + str(self.get_val_f))

            if iff is not None:
                if isinstance(iff, expr):
                    self.iff = iff.em
                elif isinstance(iff, (type_enum,type_base)):
                    iff.to_expr()
                    self.iff = pop_expr()
                elif callable(iff):
                    # The user has provided a function to
                    # gate when sampling occurs
                    self.iff_f = iff
                else:
                    raise Exception("Unknown iff type " + str(iff))
            
        self.bins = bins
        self.ignore_bins = ignore_bins
        self.illegal_bins = illegal_bins
        
        ctor.clear_exprs()
        
    def get_coverage(self):
        if self.model is None:
            return 0.0
        else:
            return self.model.get_coverage()
    
    def get_inst_coverage(self):
        if self.model is None:
            return 0.0
        else:
            return self.model.get_inst_coverage()
    
    def build_cov_model(self, parent, name):
        if self.model is None:
            options = self.options.create_model(parent.options)
            if self.get_val_f is not None:
                if self.cp_t is not None and isinstance(self.cp_t, type_base):
                    width = self.cp_t.width
                    is_signed = self.cp_t.is_signed
                else:
                    width = 32
                    is_signed = True
                    
                sample_expr = ExprRefModel(
                    self.get_val_f, 
                    width,
                    is_signed)
            else:
                sample_expr = self.target
                
            iff_e = None
            if self.iff_f is not None:
                iff_e = ExprRefModel(self.iff_f, 1, False)
            elif self.iff is not None:
                iff_e = self.iff
            
            self.model = CoverpointModel(
                sample_expr,
                name if self.name is None else self.name,
                options,
                iff_e)
            self.model.srcinfo_decl = self.srcinfo_decl

            with expr_mode():
                exclude_bins = RangelistModel()
                
                if self.ignore_bins is not None:
                    if not isinstance(self.ignore_bins, dict):
                        raise Exception("ignore_bins must be a 'dict'")
                    
                    for ib_name in self.ignore_bins.keys():
                        ib = self.ignore_bins[ib_name]
                        if isinstance(ib, bin):
                            for r in ib.range_l:
                                if isinstance(r, (dict,tuple)):
                                    exclude_bins.add_range(r[0], r[1])
                                else:
                                    exclude_bins.add_value(r)
                        else:
                            raise Exception("ignore_bins only supports 'bin' elements")
                        
                if self.illegal_bins is not None:
                    if not isinstance(self.illegal_bins, dict):
                        raise Exception("illegal_bins must be a 'dict'")
                    
                    for ib_name in self.illegal_bins.keys():
                        ib = self.illegal_bins[ib_name]
                        if isinstance(ib, bin):
                            for r in ib.range_l:
                                if isinstance(r, (dict,tuple)):
                                    exclude_bins.add_range(r[0], r[1])
                                else:
                                    exclude_bins.add_value(r)
                        else:
                            raise Exception("ignore_bins only supports 'bin' elements")
                        
                if len(exclude_bins.range_l) > 0:
                    exclude_bins.compact()
                
                # TODO: handle illegal_bins in the future
                
                if self.bins is None or len(self.bins) == 0:
                    if isinstance(self.cp_t, type_enum):
                        ei = self.cp_t.enum_i
                        enum_bins = RangelistModel()
                        for e,v in ei.e2v_m.items():
                            enum_bins.add_value(v)

                        # Ensure that they're ordered
                        enum_bins.compact()
                        
                        if len(exclude_bins.range_l) > 0:
                            enum_bins.intersect(exclude_bins)

                        for v in enum_bins.range_l:                        
                            e = ei.v2e_m[v[0]]
                            self.model.add_bin_model(CoverpointBinEnumModel(str(e), v[0]))
                            
                    elif isinstance(self.cp_t, type_base):
                        binspec = RangelistModel()
                        if not self.cp_t.is_signed:
                            binspec.add_range(0, (1 << self.cp_t.width)-1)
                        else:
                            low = (1 << self.cp_t.width-1)
                            high = (1 << self.cp_t.width-1)-1
                            binspec.add_range(-low, high)
                            
                        if len(exclude_bins.range_l) > 0:
                            # Need to trim bins
                            exclude_bins.compact()
                            binspec.intersect(exclude_bins)

                        self.model.add_bin_model(CoverpointBinCollectionModel.mk_collection(
                            name, binspec, options.auto_bin_max))
                    else:
                        raise Exception("attempting to create auto-bins from unknown type " + str(self.cp_t))
                else:
                    # TODO: need a pre-step where we build the ranges, then trim
                    for bin_name,bin_spec in self.bins.items():
                        if not hasattr(bin_spec, "build_cov_model"):
                            raise Exception("Bin specification doesn't have a build_cov_model method")
                        bin_m = bin_spec.build_cov_model(self.model, bin_name, exclude_bins)
                        self.model.add_bin_model(bin_m)
                        
                if self.ignore_bins is not None and len(self.ignore_bins) != 0:
                    # Build dedicated ignore_bins
                    for bin_name,bin_spec in self.ignore_bins.items():
                        if not hasattr(bin_spec, "build_cov_model"):
                            raise Exception("Bin specification doesn't have a build_cov_model method")
                        bin_m = bin_spec.build_cov_model(self.model, bin_name, None)
                        self.model.add_ignore_bin_model(bin_m)
                if self.illegal_bins is not None and len(self.illegal_bins) != 0:
                    # Build dedicated ignore_bins
                    for bin_name,bin_spec in self.illegal_bins.items():
                        if not hasattr(bin_spec, "build_cov_model"):
                            raise Exception("Bin specification doesn't have a build_cov_model method")
                        bin_m = bin_spec.build_cov_model(self.model, bin_name, None)
                        self.model.add_illegal_bin_model(bin_m)

        return self.model
    
    def get_model(self):
        return self.model
    
    def get_val(self, cp_m):
        ret = int(self.get_val_f())
        return ret
    
    def set_val(self, val):
        self.target.set_val(val)
    
    def __le__(self, rhs):
        if self.have_var:
            self.target(rhs)
        else:
            raise Exception("Attempting to set value of non-variable coverpoint")
        
    def _lock(self):
        self.options.lock()
        self.type_options._lock()
    
class cross(object):
    
    def __init__(self, 
                 target_l, 
                 bins=None, 
                 options=None,
                 name=None,
                 iff=None):
        for t in target_l:
            if not isinstance(t, coverpoint):
                raise Exception("Cross target \"" + str(t) + "\" is not a coverpoint")
        self.target_l = target_l
        self.bins = bins
        self.options = Options()
        
        if options is not None:
            self.options.set(options)
        
        self.iff_f = None
        self.iff = None

        if iff is not None:        
            with expr_mode():
                if isinstance(iff, expr):
                    self.iff = iff.em
                elif isinstance(iff, (type_enum,type_base)):
                    iff.to_expr()
                    self.iff = pop_expr()
                elif callable(iff):
                    self.iff_f = iff
                else:
                    raise Exception("Unknown iff type " + str(iff))
        
        # Capture the declaration location of this cross
        frame = inspect.stack()[1]
        self.srcinfo_decl = SourceInfo(frame.filename, frame.lineno)
        self.name = name
        
        self.model = None
        
    def build_cov_model(self, parent, name):
        # Let the user-specified name take precedence
        if self.model is None:
            iff = None
            options = self.options.create_model(parent.options)

            if self.iff_f:
                iff = ExprRefModel(self.iff_f, 1, False)
            elif self.iff:
                iff = self.iff
            
            ret = CoverpointCrossModel(
                name if self.name is None else self.name,
                options,
                iff)
        
            ret.srcinfo_decl = self.srcinfo_decl
        
            for cp in self.target_l:
                m = cp.get_model()
                ret.add_coverpoint(m)
                
            self.model = ret
            
        return self.model
    
    def get_coverage(self):
        if self.model is None:
            return 0.0
        else:
            return self.model.get_coverage()        
