

# Created on Mar 27, 2020
#
# @author: ballance


class RandGenData(object):
    
    def __init__(self, width, is_signed):
        self.width = width
        self.is_signed = is_signed
        self.bag = None
        # Tracks whether we've actually computed the min/max, 
        # or if we're using the wide-open domain
        self.found_min_max = False
        
        # This field is queued for min/max discovery
        self.find_min_max = False

        if is_signed:
            self.min = -(1 << width-1)
            self.max = (1 << width-1)-1
        else:
            self.min = 0
            self.max = (1 << width)-1
