'''
Created on Jan 12, 2020

@author: ballance
'''
from enum import IntEnum, auto

class ToggleMetricT(IntEnum):
    NOBINS     = 1         # Toggle scope has no local bins
    ENUM       = auto()    # UCIS:ENUM
    TRANSITION = auto()    # UCIS:TRANSITION
    _2STOGGLE  = auto()    # UCIS:2STOGGLE
    ZTOGGLE    = auto()    # UCIS:ZTOGGLE
    XTOGGLE    = auto()    # UCIS:XTOGGLE
