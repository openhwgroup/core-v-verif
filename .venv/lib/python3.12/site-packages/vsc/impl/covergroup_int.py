
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

'''
Created on Feb 7, 2020

@author: ballance
'''
from vsc.impl.expr_mode import enter_expr_mode, leave_expr_mode

class CovergroupInt():
    """Internal data used by a covergroup """
    
    def __init__(self, facade_obj):
        self.fo = facade_obj
        self.sample_var_l = []
        self.sample_obj_l = []
        self.model = None
        self.ctor_level = 0
        self.locked = False
        self.srcinfo_inst = None
        pass
    
    def __enter__(self):
        enter_expr_mode()
        self.ctor_level += 1
        
    def __exit__(self, t, v, tb):
        leave_expr_mode()
        self.ctor_level -= 1
        