from vsc.model.coverage_options_model import CoverageOptionsModel

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

class Options():
    
    def __init__(self):
        self.locked = False
        self.name = None
        self.weight = None
        self.goal = None
        self.comment = None
        self.at_least = None
        self.auto_bin_max = None
        self.cross_num_print_missing = None
        self.detect_overlap = None
        self.per_instance = None
        self.get_inst_coverage = None

    def set(self, values):
        for key in values.keys():
            if not hasattr(self, key):
                raise AttributeError("Option %s is invalid" % (key))
            setattr(self, key, values[key])
    
    def __setattr__(self, field, val):
        if field == "locked" and hasattr(self, "locked") and self.locked:
            raise Exception("Failed to set option \"%s\" since covergroup is locked" % (field))
        object.__setattr__(self, field, val)
        
    def lock(self):
        self.locked = True
        
    def create_model(self, parent=None):
        ret = CoverageOptionsModel()
        
        if self.weight is not None:
            ret.weight = self.weight
        elif parent is not None:
            ret.weight = parent.weight
            
        if self.goal is not None:
            ret.goal = self.goal
        elif parent is not None:
            ret.goal = parent.goal

        # Comment doesn't cascade        
        if self.comment is not None:
            ret.comment = self.comment
            
        if self.at_least is not None:
            ret.at_least = self.at_least
        elif parent is not None:
            ret.at_least = parent.at_least
            
        if self.auto_bin_max is not None:
            ret.auto_bin_max = self.auto_bin_max
        elif parent is not None:
            ret.auto_bin_max = parent.auto_bin_max
            
        return ret
            
        
    def propagate(self, options_m):
        options_m.weight = self.weight
        options_m.at_least = self.at_least
        options_m.goal = self.goal
        
