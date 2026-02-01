'''
Created on Mar 12, 2020

@author: ballance
'''

from _ctypes import Structure
from ctypes import c_int, c_ulonglong, c_uint, c_wchar_p, c_double, c_wchar
from ucis.test_data import TestData

class LibTestData(Structure):
    _fields_ = [
        ("teststatus", c_uint),
        ("simtime", c_double),
        ("timeunit", c_wchar_p),
        ("runcwd", c_wchar_p),
        ("cputime", c_double),
        ("seed", c_wchar_p),
        ("cmd", c_wchar_p),
        ("args", c_wchar_p),
        ("compulsory", c_int),
        ("date", c_wchar_p),
        ("username", c_wchar_p),
        ("cost", c_double),
        ("toolcategory", c_wchar_p)
    ]

    @staticmethod
    def ctor(td : TestData):
        
        ret = LibTestData(
            td.teststatus,
            td.simtime,
            td.timeunit,
            td.runcwd,
            td.cputime,
            td.seed,
            td.cmd,
            td.args,
            td.compulsory,
            td.date,
            td.user,
            td.cost,
            td.toolcategory
            )        
        
#         ret = LibTestData(
#             td.teststatus,
#             td.simtime,
#             None if td.timeunit is None else str.encode(td.timeunit),
#             None if td.runcwd is None else str.encode(td.runcwd),
#             td.cputime,
#             None if td.seed is None else str.encode(td.seed),
#             None if td.cmd is None else str.encode(td.cmd),
#             None if td.args is None else str.encode(td.args),
#             td.compulsory,
#             None if td.date is None else str.encode(td.date),
#             None if td.user is None else str.encode(td.user),
#             td.cost,
#             None if td.toolcategory is None else str.encode(td.toolcategory)
#             )
        
        return ret
   
    def to_testdata(self):
        ret = TestData(
            self.teststatus,
            self.simtime,
            self.timeunit,
            self.runcwd,
            self.cputime,
            self.seed,
            self.cmd,
            self.args,
            self.compulsory,
            self.date,
            self.username,
            self.cost,
            self.toolcategory)
        
        return ret

    