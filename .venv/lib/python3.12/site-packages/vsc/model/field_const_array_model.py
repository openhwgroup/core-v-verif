'''
Created on Jun 21, 2020

@author: ballance
'''
from vsc.model.field_array_model import FieldArrayModel

class FieldConstArrayModel(FieldArrayModel):
    
    def __init__(self, name, data):
        super().__init__(name, True, None, 32, False, False, False)
        
        # Create elements from the data
        max_v = max(data)
        min_v = min(data)
        
        if max_v < 0 or min_v < 0:
            self.is_signed = True
            
        else:
            self.width = 1
            while max_v > 0:
                self.width += 1
                max_v >>= 1
                
        # Create fields to match
        for v in data:
            f = self.add_field()
            f.set_val(v)
        self.size.set_val(len(data))
            
        