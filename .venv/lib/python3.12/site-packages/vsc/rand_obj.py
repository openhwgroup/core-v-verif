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

import inspect

from vsc.impl.randobj_int import RandObjInt
from vsc.constraints import constraint_t, dynamic_constraint_t
from vsc.impl.ctor import push_constraint_scope, pop_constraint_scope, \
    clear_exprs, push_srcinfo_mode, pop_srcinfo_mode, in_srcinfo_mode
from vsc.impl.generator_int import GeneratorInt
from vsc.impl.expr_mode import _expr_mode, get_expr_mode, expr_mode, get_expr_mode_depth, \
    enter_expr_mode, leave_expr_mode, is_raw_mode, is_expr_mode
from vsc.model.field_composite_model import FieldCompositeModel
from vsc.model.constraint_block_model import ConstraintBlockModel
from vsc.model.randomizer import Randomizer
from vsc.model.field_scalar_model import FieldScalarModel
from vsc.model.source_info import SourceInfo
from vsc.types import type_base, field_info, list_t
from vsc.model.solve_failure import SolveFailure
from vsc.impl.constraint_proxy import ConstraintProxy


class _randobj:
    """Mark a class as randomizable"""

    def __init__(self, kwargs):
        self.srcinfo = False
        
        for kw in kwargs.keys():
            if kw == "srcinfo":
                self.srcinfo = kwargs[kw]
            else:
                raise Exception("Unknown randobj kwarg: %s" % kw)

    
    def __call__(self, T):
        
        srcinfo = self.srcinfo
    
        class randobj_interposer(T):
            
            def __init__(self, *args, **kwargs):
                ro_i = self._get_ro_int()
                ro_i.srcinfo = srcinfo
                
                # Capture the instantiation location
                frame = inspect.stack()[1]
                ro_i.srcinfo_inst = SourceInfo(frame.filename, frame.lineno)
    
                # Initialize the field_info member before going deeper            
                if ro_i.ctor_level == 0:
                    self.tname = T.__qualname__
                    self._int_field_info = field_info()
                    
                    # Decide whether to record sourceinfo for this class
                    push_srcinfo_mode(srcinfo)
                    
                # Call the user's constructor
                ro_i.ctor_level += 1
                super().__init__(*args, **kwargs)
                ro_i.ctor_level -= 1
                
                if ro_i.ctor_level == 0:
                    self.build_field_model(None)
                    pop_srcinfo_mode()
            
        # Add the interposer class
        ret = type(T.__name__, (randobj_interposer,), dict())
        
        if not hasattr(T, "_ro_init"):
            def __getattribute__(self, a):
                ret = object.__getattribute__(self, a)
            
                if isinstance(ret, type_base) and not is_raw_mode():
                    # We're not in an expression, so the user
                    # wants the value of this field
                    ret = ret.get_val()
                elif a == "rand_mode":
                    ret = self._int_rand_info.rand_mode
                elif isinstance(ret, (constraint_t,dynamic_constraint_t)):
                    if not is_expr_mode():
                        # The constraint_t wrapper is per-type. In regular
                        # procedural code we need to return a reference 
                        # to the instance object. The proxy provides a 
                        # way to do so.
                        model = object.__getattribute__(self, "get_model")()
                        cm = model.get_constraint(a)
                        ret = ConstraintProxy(cm)
                
                return ret
        
            def __setattr__(self, field, val):
                try:
                    # Retrieve the field object so we can check if it's 
                    # a type_base object. This will throw an exception
                    # if the field doesn't exist
                    fo = object.__getattribute__(self, field)
                except:
                    object.__setattr__(self, field, val)
                else:
                    if isinstance(fo, type_base):
                        if not is_raw_mode():
                            # We're not in an expression context, so the 
                            # user really wants us to set the actual value
                            # of the field
                            if isinstance(val, type_base):
                                # Looks like we're re-assigning it. 
                                if self._get_ro_int().ctor_level > 0:
                                    object.__setattr__(self, field, val)
                                else:
                                    raise Exception("Cannot re-construct field")
                            else:
                                fo.set_val(val)
                        else:
                            raise Exception("Attempting to use '=' in a constraint")
                    elif isinstance(fo, list_t):
                        fo.clear()
                        for i in val:
                            fo.append(i)
                    elif field == "rand_mode":
                        self._int_rand_info.rand_mode = bool(val)
                    else:
                        object.__setattr__(self, field, val)

            def get_randstate(self):
                ro_int = self._get_ro_int()

                # Return a copy to the user                
                return ro_int.get_randstate().clone()
            
            def set_randstate(self, rs):
                ro_int = self._get_ro_int()
                ro_int.set_randstate(rs)

            def randomize(self, 
                          debug=0,
                          lint=0,
                          solve_fail_debug=0):
                ro_int = self._get_ro_int()
                frame = inspect.stack()[1]
                
                model = self.get_model()
                try:
                    Randomizer.do_randomize(
                        ro_int.get_randstate(),
                        SourceInfo(frame.filename, frame.lineno),
                        [model], 
                        debug=debug,
                        lint=lint,
                        solve_fail_debug=solve_fail_debug)
                except SolveFailure as e:
                    print(e.diagnostics)
                    raise e
                
            def build_field_model(self, name):
                if self._int_field_info.model is None:
                    model = FieldCompositeModel(name, self._int_field_info.is_rand, self)
                    model.typename = T.__qualname__
                    self._int_field_info.model = model
                
                    # Iterate through the fields and constraints
                    # First, assign IDs to each of the randomized fields
                    with expr_mode():
                        for f in dir(self):
                            if not f.startswith("__") and not f.startswith("_int"):
                                fo = getattr(self, f)
                            
                                if hasattr(fo, "_int_field_info"):
                                    if fo._int_field_info.model is None:
                                        fo._int_field_info.model = fo.build_field_model(f)
                                    else:
                                        # Some fields may already be created, and will
                                        # have been given a placeholder name. Back-annotate
                                        # the proper name now
                                        fo._int_field_info.model.name = f
                                    fo._int_field_info.parent = self._int_field_info
    
                                    model.add_field(fo._int_field_info.model)
                    
                                # Now, elaborate the constraints
                        for f in dir(self):
                            if not f.startswith("__") and not f.startswith("_int"):
                                fo = getattr(self, f)
                                if isinstance(fo, constraint_t):
                                    clear_exprs()
                                    block = ConstraintBlockModel(f)
                                    block.srcinfo = fo.srcinfo
                                    push_constraint_scope(block)
                                    try:
                                        fo.c(self)
                                    except Exception as e:
                                        print("Exception while processing constraint: " + str(e))
                                        raise e
                                    fo.set_model(pop_constraint_scope())
                                    model.add_constraint(fo.model)
                                    clear_exprs()
                                elif isinstance(fo, dynamic_constraint_t):
                                    clear_exprs()
                                    block = ConstraintBlockModel(f)
                                    block.srcinfo = fo.srcinfo
                                    push_constraint_scope(block)
                                    try:
                                        fo.c(self)
                                    except Exception as e:
                                        print("Exception while processing constraint: " + str(e))
                                        raise e
                                    fo.set_model(pop_constraint_scope())
                                    fo.model.is_dynamic = True
                                    model.add_dynamic_constraint(fo.model)
                                    clear_exprs()
    
                self._int_field_info.model.name = name
                return self._int_field_info.model
            
            def get_model(self):
                with expr_mode():
                    if self._int_field_info.model is None:
                        self._int_field_info.model = self.build_field_model(None)
                    
                return self._int_field_info.model
            
            def _get_ro_int(self):
                if not hasattr(self, "_ro_int"):
                    self._ro_int = RandObjInt()
                return self._ro_int
            
            def __enter__(self):
                ro_i = self._get_ro_int()
                enter_expr_mode()
                self.get_model() # Ensure model is constructed
                push_srcinfo_mode(ro_i.srcinfo)
                push_constraint_scope(ConstraintBlockModel("inline"))
                return self
            
            def __exit__(self, t, v, tb):
                ro_i = self._get_ro_int()
                frame = inspect.stack()[1]
                c = pop_constraint_scope()
                leave_expr_mode()
                pop_srcinfo_mode()
                model = self.get_model() # Ensure model is constructed
                try:
                    Randomizer.do_randomize(
                        ro_i.get_randstate(),
                        SourceInfo(frame.filename, frame.lineno),
                        [model], 
                        [c], 
                        debug=self.debug,
                        lint=self.lint,
                        solve_fail_debug=self.solve_fail_debug)
                except SolveFailure as e:
                    print(e.diagnostics)
                    raise e
            
            def randomize_with(self, 
                               debug=0, 
                               lint=0,
                               solve_fail_debug=0):
                # Ensure the 'model' data structures have been built
                self.get_model()
                self.debug = debug
                self.lint = lint
                self.solve_fail_debug = solve_fail_debug
        
                return self
            
            def do_pre_randomize(self): 
                if hasattr(self, "pre_randomize"):
                    self.pre_randomize()
            
            def do_post_randomize(self):
                if hasattr(self, "post_randomize"):
                    self.post_randomize()
            
            def _id_fields(self, it, parent):
                """Apply an ID to all fields so they can be 
                referenced using indexed expressions
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
    
            setattr(T, "__getattribute__", __getattribute__)
            setattr(T, "__setattr__", __setattr__)
            setattr(T, "randomize", randomize)
            setattr(T, "randomize_with", randomize_with)
            setattr(T, "build_field_model", build_field_model)
            setattr(T, "get_model", get_model)
            setattr(T, "set_randstate", set_randstate)
            setattr(T, "get_randstate", get_randstate)
            setattr(T, "_get_ro_int", _get_ro_int)
            setattr(T, "__enter__", __enter__)
            setattr(T, "__exit__", __exit__)
            setattr(T, "do_pre_randomize", do_pre_randomize)
            setattr(T, "do_post_randomize", do_post_randomize)
            setattr(T, "_id_fields", _id_fields)
            setattr(T, "_ro_init", True)
            
        return ret

def randobj(*args, **kwargs):
    if len(args) == 1 and len(kwargs) == 0 and callable(args[0]):
        # Called without arguments
        obj = _randobj({})
        return obj(args[0])
    else:
        obj = _randobj(kwargs)
        return obj

def generator(T):
    """Mark a class as a generator"""
    
    class generator_interposer(T):
        
        def __init__(self, *args, **kwargs):
            gen_i = self._get_int()
            
            # Capture the instantiation location
            frame = inspect.stack()[1]
            gen_i.srcinfo_inst = SourceInfo(frame.filename, frame.lineno)

            # Call the user's constructor            
            with gen_i:
                super().__init__(*args, **kwargs)

            self._int_field_info = field_info()                
            if gen_i.ctor_level == 0:
                self.build_model()
            
            pass

    # Add the interposer class    
    ret = type(T.__name__, (generator_interposer,), dict())

    if not hasattr(T, "_gen_init"):
        def __getattribute__(self, a):
            ret = object.__getattribute__(self, a)
        
            if isinstance(ret, type_base) and not is_raw_mode():
                # We're not in an expression, so the user
                # wants the value of this field
                ret = ret.get_val()
            
            return ret
    
        def __setattr__(self, field, val):
            try:
                # Retrieve the field object so we can check if it's 
                # a type_base object. This will throw an exception
                # if the field doesn't exist
                fo = object.__getattribute__(self, field)
            except:
                object.__setattr__(self, field, val)
            else:
                if isinstance(fo, type_base):
                    if not is_raw_mode():
                        # We're not in an expression context, so the 
                        # user really wants us to set the actual value
                        # of the field
                        fo.set_val(val)
                    else:
                        raise Exception("Attempting to use '=' in a constraint")
                else:
                    object.__setattr__(self, field, val)                
                    
        def randomize(self):
            model = self.get_model()
            Randomizer.do_randomize([model])
            
        def build_field_model(self, name):
            if self._int_field_info.model is None:
                model = FieldCompositeModel(name, self._int_field_info.is_rand, self)
                model.typename = T.__name__
                self._int_field_info.model = model
            
                # Iterate through the fields and constraints
                # First, assign IDs to each of the randomized fields
                with expr_mode():
                    for f in dir(self):
                        if not f.startswith("__") and not f.startswith("_int"):
                            fo = getattr(self, f)
                        
                            if hasattr(fo, "_int_field_info"):
                                if fo._int_field_info.model is None:
                                    fo._int_field_info.model = fo.build_field_model(f)

                                model.add_field(fo._int_field_info.model)
                
                            # Now, elaborate the constraints
                    for f in dir(self):
                        if not f.startswith("__") and not f.startswith("_int"):
                            fo = getattr(self, f)
                            if isinstance(fo, constraint_t):
                                clear_exprs()
                                block = ConstraintBlockModel(f)
                                block.srcinfo = fo.srcinfo
                                push_constraint_scope(block)
                                try:
                                    fo.c(self)
                                except Exception as e:
                                    print("Exception while processing constraint: " + str(e))
                                    raise e
                                fo.set_model(pop_constraint_scope())
                                model.add_constraint(fo.model)
                                clear_exprs()
                                    
            self._int_field_info.model.name = name
            return self._int_field_info.model
        
        def get_model(self):
            with expr_mode():
                if self._int_field_info.model is None:
                    self._int_field_info.model = self.build_field_model(None)
                
            return self._int_field_info.model
        
        def _get_int(self):
            if not hasattr(self, "_gen_int"):
                self._gen_int = GeneratorInt()
            return self._gen_int
        
        setattr(T, "__getattribute__", __getattribute__)
        setattr(T, "__setattr__", __setattr__)
        setattr(T, "randomize", randomize)
#        setattr(T, "randomize_with", randomize_with)
        setattr(T, "build_field_model", build_field_model)
        setattr(T, "get_model", get_model)
#        setattr(T, "__enter__", __enter__)
#        setattr(T, "__exit__", __exit__)
#        setattr(T, "do_pre_randomize", do_pre_randomize)
#        setattr(T, "do_post_randomize", do_post_randomize)
        setattr(T, "_int_field_info", field_info(True))
        setattr(T, "_get_int", _get_int)
        setattr(T, "_ro_init", True)
    
        
        
    
    return ret

