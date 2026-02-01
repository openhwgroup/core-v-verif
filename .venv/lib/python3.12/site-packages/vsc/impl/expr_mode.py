'''
Created on Mar 29, 2020

@author: ballance
'''

_expr_mode = []
_raw_mode = []

def get_expr_mode():
    return (len(_expr_mode) > 0 and _expr_mode[-1])

def get_expr_mode_depth():
    return len(_expr_mode)

def enter_expr_mode(is_expr_mode=True):
    _expr_mode.append(is_expr_mode)
    
def leave_expr_mode():
    _expr_mode.pop()

def enter_raw_mode(is_raw_mode=True):
    _raw_mode.append(is_raw_mode)
    
def leave_raw_mode():
    _raw_mode.pop()

class expr_mode(object):
    
    def __enter__(self, is_expr_mode=True):
        enter_expr_mode(is_expr_mode)
        
    def __exit__(self, t, v, tb):
        leave_expr_mode()

def is_raw_mode():
    return (len(_expr_mode) > 0 and _expr_mode[-1]) or (len(_raw_mode) > 0 and _raw_mode[-1])
        
def is_expr_mode():
    return (len(_expr_mode) > 0 and _expr_mode[-1])