
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

from builtins import callable
import inspect
import random

from vsc.constraints import weight
from vsc.impl import expr_mode
from vsc.impl.ctor import push_constraint_scope, pop_constraint_scope
from vsc.impl.expr_mode import enter_raw_mode, leave_raw_mode, enter_expr_mode, \
    leave_expr_mode
from vsc.model.constraint_block_model import ConstraintBlockModel
from vsc.model.randomizer import Randomizer
from vsc.model.solve_failure import SolveFailure
from vsc.model.source_info import SourceInfo
from vsc.types import field_info, type_base
from vsc.model.rand_state import RandState


_solve_fail_debug = False

def randomize_with(*args, **kwargs):
    """Randomize a list of variables with an inline constraint"""
    field_l = []
    for v in args:
        if not hasattr(v, "get_model"):
            raise Exception("Parameter \"" + str(v) + " to randomize is not a vsc object")
        field_l.append(v.get_model())

    debug=0
    if "debug" in kwargs.keys():
        debug = kwargs["debug"]
        
    solve_fail_debug = False
    if "solve_fail_debug" in kwargs:
        solve_fail_debug = kwargs["solve_fail_debug"]
        
    randstate = None
    if "randstate" in kwargs:
        randstate = kwargs["randstate"]
    else:
        randstate = RandState(random.randint(0,0xFFFFFFFF))
    
    class inline_constraint_collector(object):
        
        def __init__(self, 
                     randstate,
                     field_l, 
                     solve_fail_debug):
            self.randstate = randstate
            self.field_l = field_l
            self.solve_fail_debug = solve_fail_debug
        
        def __enter__(self):
            # Go into 'expression' mode
            enter_expr_mode()
            push_constraint_scope(ConstraintBlockModel("inline"))
            return self
        
        def __exit__(self, t, v, tb):
            frame = inspect.stack()[1]
            c = pop_constraint_scope()
            leave_expr_mode()
          
            try:
                Randomizer.do_randomize(
                    self.randstate,
                    SourceInfo(frame.filename, frame.lineno),
                    self.field_l, 
                    [c], 
                    debug=debug)
            except SolveFailure as e:
                if _solve_fail_debug or self.solve_fail_debug:
                    print("Solve Failure")
                raise e
    
    return inline_constraint_collector(
        randstate, field_l, solve_fail_debug)

def randomize(*args,**kwargs):
    """Randomize a list of variables"""
    frame = inspect.stack()[1]
    fields = []
    for v in args:
        if hasattr(v, "get_model"):
            fields.append(v.get_model());
        else:
            raise Exception("Parameter \"" + str(v) + " to randomize is not a vsc object")
        
    debug=0
    if "debug" in kwargs.keys():
        debug=kwargs["debug"]
        
    solve_fail_debug = False
    if "solve_fail_debug" in kwargs:
        solve_fail_debug = kwargs["solve_fail_debug"]
        
    randstate = None
    if "randstate" in kwargs:
        randstate = kwargs["randstate"]
    else:
        randstate = RandState(random.randint(0,0xFFFFFFFF))
        
    Randomizer.do_randomize(
        randstate,
        SourceInfo(frame.filename, frame.lineno),
        fields, 
        solve_fail_debug=solve_fail_debug,
        debug=debug)

class raw_mode(object):
    """Raw mode provides raw access to primitive VSC Fields"""
    
    def __enter__(self):
        enter_raw_mode()
    
    def __exit__(self, t, v, tb):
        leave_raw_mode()

def randselect(sel_l):
    """Randomly select and call a lambda"""
    if not isinstance(sel_l, list):
        raise Exception("randselect requires a list of tuples")

    weight_v = []    
    for i,e in enumerate(sel_l):
        if not isinstance(e, (tuple,list)):
            raise Exception("Element " + str(i) + " is not a list or tuple (" + 
                            str(type(e)))
        if not callable(e[1]):
            raise Exception("Element " + str(i) + " does not specify a callable element")
        weight_v.append(int(e[0]))
        
    idx = distselect(weight_v)
    
    # Invoke the method
    sel_l[idx][1]()

def distselect(weight_l):
    """Perform a weighted selection using the weights 
    from the provided list. Return the selected index"""

    if not isinstance(weight_l, list):
        raise Exception("distselect requires a list of values")

    # Create a weight/index vector
    weight_v = []
    total_w = 0
    for i,v in enumerate(weight_l):
        w = int(v)
        total_w += w
        weight_v.append((w, i))
        
    # Order by weight value
    weight_v.sort(key=lambda e:e[0])
    
    rand_v = random.randint(1, total_w)
    
    for we in weight_v:
        rand_v -= we[0]
        
        if rand_v <= 0:
            # Return the selected index
            return we[1]

    # Return the last index
    return weight_v[-1][1]
    
    