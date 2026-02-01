
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

class TypeOptions():
    
    def __init__(self):
        self.locked = False
        self.weight = 1
        self.goal = 100
        self.comment = ""
        self.merge_instances = False
        self.distribute_first = False
        
    def set(self, values):
        for key in values.keys():
            if not hasattr(self, key):
                raise AttributeError("Option %s is invalid" % (key))
            setattr(self, key, values[key])
    
    def __setattr__(self, field, val):
        if field == "locked" and hasattr(self, "locked") and self.locked:
            raise Exception("Failed to set option \"%s\" since covergroup is locked" % (field))
        object.__setattr__(self, field, val)
        
    def _lock(self):
        self.locked = True
        