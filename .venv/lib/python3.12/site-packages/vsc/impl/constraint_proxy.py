'''
Created on Jun 16, 2021

@author: mballance
'''

class ConstraintProxy(object):
    """Proxy object typically used when calling 'constraint_mode'"""
    
    def __init__(self, m):
        self.constraint_model = m
        
    def constraint_mode(self, en):
        self.enabled = en
        if self.constraint_model is not None:
            self.constraint_model.set_constraint_enabled(en)
        
        