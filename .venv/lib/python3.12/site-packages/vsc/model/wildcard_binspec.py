'''
Created on Jul 23, 2021

@author: mballance
'''

class WildcardBinspec(object):
    
    def __init__(self, specs):
        
        self.specs = []
        for s in specs:
            self.specs.append((s[0], s[1]))
        
    def equals(self, oth):
        
        eq = isinstance(oth, WildcardBinspec)
        
        if eq:
            eq &= len(self.specs) == len(oth.specs)
            
            if eq:
                for i in range(len(self.specs)):
                    eq &= self.specs[i] == oth.specs[i]
                    if not eq:
                        break
                    
        return eq
    
    def clone(self):
        return WildcardBinspec(self.specs)
