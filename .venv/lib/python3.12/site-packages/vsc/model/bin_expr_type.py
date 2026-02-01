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


# Created on Jul 26, 2019
#
# @author: ballance


from enum import Enum, auto

class BinExprType(Enum):
    Eq = auto()
    Ne = auto()
    Gt = auto()
    Ge = auto()
    Lt = auto()
    Le = auto()
    Add = auto()
    Sub = auto()
    Div = auto()
    Mul = auto()
    Mod = auto()
    And = auto()
    Or = auto()
    Sll = auto()
    Srl = auto()
    Xor = auto()
    Not = auto()
    
    @staticmethod
    def toString(op):
        return {
            BinExprType.Eq : "==",
            BinExprType.Ne : "!=",
            BinExprType.Gt : ">",
            BinExprType.Ge : ">=",
            BinExprType.Lt : "<",
            BinExprType.Le : "<=",
            BinExprType.Add : "+",
            BinExprType.Sub : "-",
            BinExprType.Div : "/",
            BinExprType.Mul : "*",
            BinExprType.Mod : "%",
            BinExprType.And : "&",
            BinExprType.Or  : "|",
            BinExprType.Sll : "<<",
            BinExprType.Srl : ">>",
            BinExprType.Xor : "^",
            BinExprType.Not : "!",
            }[op]
        
    