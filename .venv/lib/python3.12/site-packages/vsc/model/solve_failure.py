'''
Created on Sep 9, 2020

@author: ballance
'''

class SolveFailure(Exception):
    
    def __init__(self, msg, diagnostics):
        super().__init__(msg)
        self.diagnostics = diagnostics

