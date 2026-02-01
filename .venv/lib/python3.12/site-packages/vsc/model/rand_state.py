'''
Created on Oct 12, 2021

@author: mballance
'''
import random

class RandState(object):
    
    def __init__(self, seed):
        # Ensure no zero seeds
        self.state = abs(seed)+1
        pass
    
    def clone(self) -> 'RandState':
        return RandState(self.state)
    
    def rand_u(self):
        val = self.state
        val ^= val << 13
        val ^= val >> 7
        val ^= val << 17
        val &= 0xFFFFFFFFFFFFFFFF
        self.state = val
        return val
    
    def rand_s(self):
        val = self.rand_u()
        
        if (val&(1 << 63)) != 0:
            # Negative number
            val = -((~val & 0xFFFFFFFFFFFFFFFF)+1)
            
        return val
    
    def randint(self, low, high):
        low = int(low)
        high = int(high)
        
        if high < low:
            tmp = low
            low = high
            high = tmp
        
        if low == high:
            return low
        elif low >= 0 and high >= 0:
            val = self.rand_u()
            val = int(val % ((high-low)+1))
            val += low
            return val
        else:
            # One is less than zero
            val = self.rand_s()
            val = int(val % ((high-low)+1))
            val += low
            return val
    
    @classmethod
    def mk(cls):
        """Creates a random-state object using the Python random state"""
        seed = random.randint(0, 0xFFFFFFFF)
        return RandState(seed)
   
    @classmethod
    def mkFromSeed(cls, seed, strval=None):
        """Creates a random-state object from a numeric seed and optional string"""
        if strval is not None:
            seed = (seed + abs(hash(strval))) & 0xFFFFFFFF
        return RandState(seed)
        