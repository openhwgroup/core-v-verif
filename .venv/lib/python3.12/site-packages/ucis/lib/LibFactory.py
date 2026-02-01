
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
Created on Jan 10, 2020

@author: ballance
'''
from ctypes import *
from ucis.lib import libucis
from ucis.lib.libucis import _lib, get_ucis_library
from ucis.lib.lib_ucis import LibUCIS

class LibFactory():

    @staticmethod
    def create(file=None):
        if get_ucis_library() is None:
            raise Exception("libucis not loaded")
        
        return LibUCIS(file)
        

    # Load the specified UCIS library
    @staticmethod
    def load_ucis_library(lib):
        libucis.load_ucis_library(lib)
    