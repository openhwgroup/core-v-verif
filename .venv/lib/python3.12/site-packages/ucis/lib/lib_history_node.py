'''
Created on Mar 11, 2020

@author: ballance
'''
from _ctypes import pointer
from ucis import UCIS_INT_TEST_STATUS
from ucis.history_node import HistoryNode
from ucis.lib.lib_obj import LibObj
from ucis.lib.lib_scope import LibScope
from ucis.lib.libucis import get_lib
from ucis.test_data import TestData
from ucis.test_status_t import TestStatusT

from ucis.lib.lib_test_data import LibTestData


class LibHistoryNode(LibObj, HistoryNode):
    
    def __init__(self, db, hn):
        super().__init__(db, hn)
        
        
    def setTestData(self, testdata:TestData):
        lib_td = pointer(LibTestData.ctor(testdata))
        
        get_lib().ucis_SetTestData(
            self.db,
            self.obj,
            lib_td)
        
    def getTestData(self):
        lib_td = pointer(LibTestData())
        
        get_lib().ucis_SetTestData(
            self.db,
            self.obj,
            lib_td)
        
        return lib_td.to_testdata()
    
    def getTestStatus(self) -> TestStatusT:
        return self.getIntProperty(-1, UCIS_INT_TEST_STATUS)
    
    def setTestStatus(self, status : TestStatusT):
        self.setIntProperty(-1, UCIS_INT_TEST_STATUS, status)
    
        
