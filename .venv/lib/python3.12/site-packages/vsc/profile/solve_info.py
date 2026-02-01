'''
Created on Jul 3, 2021

@author: mballance
'''

class SolveInfo(object):
    
    def __init__(self):
        self.totaltime = 0
        # Number of randsets
        self.n_randsets = 0
        
        # Constrained fields
        self.n_cfields = 0

        # Time establishing SAT-ness        
        self.sat_time = 0

        # Time swizzling random fields        
        self.rnd_time = 0
        
        self.n_sat_calls = 0
        
        
        pass