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

from vsc.types import type_base, field_info, type_enum
from enum import Enum


def attr(t):
    """Wraps a recognized datatype as a non-rand field"""
    if isinstance(t, Enum):
        t = type_enum(t)
        t._int_field_info.set_is_rand(True)
    elif not hasattr(t, "_int_field_info"):
        raise Exception("Attempting to decorate \"" + str(t) + "\" of type \"" + str(type(t)) + "\" as a VSC field")
    
    return t

def rand_attr(t):
    """Wraps a VSC datatype, or recognized datatype, as a rand field"""
    if hasattr(t, "_int_field_info"):
        t._int_field_info.set_is_rand(True)
    elif isinstance(t, Enum):
        t = type_enum(t)
        t._int_field_info.set_is_rand(True)
    else:
        raise Exception("Attempting to decorate \"" + str(t) + "\" of type \"" + str(type(t)) + "\" as rand")
    
    return t
