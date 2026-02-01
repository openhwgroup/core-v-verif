

# Created on Feb 29, 2020
#
# @author: ballance


class RandObjModelIF(object):
    """Implements a callback interface to notify about randomization phases"""
    
    def do_pre_randomize(self):
        pass
    
    def do_post_randomize(self):
        pass