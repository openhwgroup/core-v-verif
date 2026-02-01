

# Created on Mar 20, 2020
#
# @author: ballance


class RandIF(object):
    """Defines operations to be implemented by a random generator"""
    
    def __init__(self):
        super().__init__()
        
    def randint(self, low:int, high:int)->int:
        raise NotImplementedError("randint not implemented for " + str(type(self)))
    
    def sample(self, s, k):
        raise NotImplementedError("sample not implemented for " + str(type(self)))
