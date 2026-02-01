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


# Created on Jul 28, 2019
#
# @author: ballance

from vsc.model.expr_rangelist_model import ExprRangelistModel
from vsc.model.expr_range_model import ExprRangeModel


from vsc.model.expr_model import ExprModel
from vsc.model.expr_bin_model import ExprBinModel
from vsc.model.bin_expr_type import BinExprType
from vsc.model.expr_fieldref_model import ExprFieldRefModel
from vsc.model.field_array_model import FieldArrayModel
from vsc.model.expr_literal_model import ExprLiteralModel

class ExprInModel(ExprModel):
    
    def __init__(self, lhs : ExprModel, rhs : ExprRangelistModel):
        super().__init__()
        self.lhs = lhs
        self.rhs = rhs
        
    def build(self, btor, ctx_width=-1):
        t = None
        expr = None
        for r in self.rhs.rl:
            if isinstance(r, ExprRangeModel):
                t = ExprBinModel(
                    ExprBinModel(self.lhs, BinExprType.Ge, r.lhs),
                    BinExprType.And,
                    ExprBinModel(self.lhs, BinExprType.Le, r.rhs))
            elif isinstance(r, ExprFieldRefModel):
                if isinstance(r.fm, FieldArrayModel):
                    # Need to build out for each element
                    # TODO: must handle case where size is random
                    arr : FieldArrayModel = r.fm
                    
                    if arr.is_rand_sz:
                        pass
                    else:
                        for i in range(int(arr.size.get_val())):
                            t = ExprBinModel(
                                self.lhs, 
                                BinExprType.Eq, 
                                ExprFieldRefModel(arr.field_l[i]))
                            if expr is None:
                                expr = t
                            else:
                                expr = ExprBinModel(expr, BinExprType.Or, t)
                        # Clear the temporary term, so the combination code
                        # below doesn't use it.
                        t = None
                else:
                    t = ExprBinModel(self.lhs, BinExprType.Eq, r)
            else:
                t = ExprBinModel(self.lhs, BinExprType.Eq, r)

            if t is not None:                
                if expr is None:
                    expr = t 
                else:
                    expr = ExprBinModel(expr, BinExprType.Or, t)

        if expr is None:
            expr = ExprLiteralModel(1, False, 1)

        from vsc.visitors.model_pretty_printer import ModelPrettyPrinter
        return expr.build(btor) if expr is not None else None
    def is_signed(self):
        return False
    
    def width(self):
        return 1
    
    def accept(self, visitor):
        visitor.visit_expr_in(self)
        
