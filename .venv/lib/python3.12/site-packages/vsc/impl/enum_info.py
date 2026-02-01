'''
Created on Mar 27, 2020

@author: ballance
'''
from typing import Dict
from enum import IntEnum, EnumMeta, Flag, Enum
from vsc.model.expr_literal_model import ExprLiteralModel

class EnumInfo(object):
    """Collects information needed by VSC"""
    
    _info_map : Dict[object,'EnumInfo'] = {}
    
    def __init__(self, e):
        self.e = e
        self.e2v_m = {}
        self.v2e_m = {}
        self.enums = []

        if isinstance(e, EnumMeta):
            i=0
            for en in e:
                # An IntEnum exposes its value via an __int__ method
                if hasattr(en, "__int__"):
                    i = int(en)
                    
                self.e2v_m[en] = i
                self.v2e_m[i] = en
                self.enums.append(i)
                i += 1
        else:
            raise Exception("unsupported enum type " + str(e))
        
    def e2v(self, ev)->int:
        return self.e2v_m[ev]
    
    def v2e(self, v):
        return self.v2e_m[int(v)]
    
    def e2e(self, ev):
        v = self.e2v_m[ev]
        return ExprLiteralModel(v, True, 32)
    
    @staticmethod
    def get(e)->'EnumInfo':
        if not e in EnumInfo._info_map.keys():
            info = EnumInfo(e)
            EnumInfo._info_map[e] = info
        else:
            info = EnumInfo._info_map[e]
            
        return info
            
            
        