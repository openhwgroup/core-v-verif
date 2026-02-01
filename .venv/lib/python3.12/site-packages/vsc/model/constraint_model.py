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

# Created on Jul 27, 2019
#
# @author: ballance

from pyboolector import BoolectorNode

class ConstraintModel(object):
    """Base class for all constraint models"""
    
    def __init__(self):
        self.node = None
        self.srcinfo = None
        pass
    
    def dispose(self):
        self.node = None
    
    def build(self, btor)->BoolectorNode:
        raise Exception("build unimplemented for constraint " + str(type(self)))
    
    def get_nodes(self, node_l):
        raise Exception("get_node unimplemented")

    @staticmethod
    def and_nodelist(node_l, btor):
        """Creates a boolean AND across a list of expression nodes"""
        ret = None
        ret_valid = False
        
        for n in node_l:
            if ret_valid:
                ret = btor.And(ret, n)
            else:
                ret = n
                ret_valid = True
        
        return ret

    def accept(self, visitor):
        raise NotImplementedError("" + str(self) + "::accept unimplemented")
    
    def clone(self, deep=False)->'ConstraintModel':
        raise NotImplementedError("clone not implemented by " + str(type(self)))
    
        
    