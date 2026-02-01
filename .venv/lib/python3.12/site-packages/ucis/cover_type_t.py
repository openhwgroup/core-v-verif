'''
Created on Jan 11, 2020

@author: ballance
'''
from enum import IntFlag

class CoverTypeT(IntFlag):
    CVGBIN      = 0x0000000000000001    # For SV Covergroups:
    COVERBIN    = 0x0000000000000002    # For cover directives- pass:
    ASSERTBIN   = 0x0000000000000004    # For assert directives- fail: 
    STMTBIN     = 0x0000000000000020    # For Code coverage(Statement):
    BRANCHBIN   = 0x0000000000000040    # For Code coverage(Branch):
    EXPRBIN     = 0x0000000000000080    # For Code coverage(Expression):
    CONDBIN     = 0x0000000000000100    # For Code coverage(Condition):
    TOGGLEBIN   = 0x0000000000000200    # For Code coverage(Toggle):
    PASSBIN     = 0x0000000000000400    # For assert directives- pass count: 
    FSMBIN      = 0x0000000000000800    # For FSM coverage:
    USERBIN     = 0x0000000000001000    # User-defined coverage:
    GENERICBIN  = USERBIN
    COUNT       = 0x0000000000002000    # user-defined count, not in coverage:
    FAILBIN     = 0x0000000000004000    # For cover directives- fail count:
    VACUOUSBIN  = 0x0000000000008000    # For assert- vacuous pass count:
    DISABLEDBIN = 0x0000000000010000    # For assert- disabled count:
    ATTEMPTBIN  = 0x0000000000020000    # For assert- attempt count:
    ACTIVEBIN   = 0x0000000000040000    # For assert- active thread count:
    IGNOREBIN   = 0x0000000000080000    # For SV Covergroups:
    ILLEGALBIN  = 0x0000000000100000    # For SV Covergroups: 
    DEFAULTBIN  = 0x0000000000200000    # For SV Covergroups: 
    PEAKACTIVEBIN = 0x0000000000400000  # For assert- peak active thread count: 
    BLOCKBIN    = 0x0000000001000000    # For Code coverage(Block):
    USERBITS    = 0x00000000FE000000    # For user-defined coverage: 
    RESERVEDBIN = 0xFF00000000000000
    
