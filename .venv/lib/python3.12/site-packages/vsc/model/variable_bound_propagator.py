'''
Created on May 30, 2020

@author: ballance
'''

class VariableBoundPropagator(object):
    
    def __init__(self, target : 'VariableBoundModel'):
        self.target = target
    
    def propagate(self):
        raise NotImplementedError("VariableBoundPropagator::propagate not implemented for " + str(type(self)))
    