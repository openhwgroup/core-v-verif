'''
Created on Jan 11, 2020

@author: ballance
'''
from enum import IntFlag

class CoverFlagsT(IntFlag):
    IS_32BIT = 0x00000001 # data is 32 bits
    IS_64BIT = 0x00000002 # data is 64 bits
    IS_VECTOR = 0x00000004 #
    HAS_GOAL = 0x00000008 #  goal included 
    HAS_WEIGHT = 0x00000010  # weight included 

# #define UCIS_EXCLUDE_PRAGMA  0x00000020  /* excluded by pragma  */
# #define UCIS_EXCLUDE_FILE    0x00000040  /* excluded by file; does not
#                                             count in total coverage */
# #define UCIS_EXCLUDE_INST    0x00000080  /* for instance-specific exclusions */
# #define UCIS_EXCLUDE_AUTO    0x00000100  /* for automatic exclusions */
# 
# #define UCIS_ENABLED         0x00000200  /* generic enabled flag; if disabled,
#                                             still counts in total coverage */
# #define UCIS_HAS_LIMIT       0x00000400  /* for limiting counts */
# #define UCIS_HAS_COUNT       0x00000800  /* has count in ucisCoverDataValueT? */
# #define UCIS_IS_COVERED      0x00001000  /* set if object is covered */
# #define UCIS_UOR_SAFE_COVERITEM        0x00002000   /* Coveritem construction is UOR compliant */
# #define UCIS_CLEAR_PRAGMA    0x00004000
# 
# /* Type-qualified flags 0x07FF0000 - flag locations may be reused for non-intersecting type sets */
# #define UCIS_HAS_ACTION      0x00010000  /* UCIS_ASSERTBIN */
# #define UCIS_IS_TLW_ENABLED  0x00020000  /* UCIS_ASSERTBIN */
# #define UCIS_LOG_ON          0x00040000  /* UCIS_COVERBIN, UCIS_ASSERTBIN */
# #define UCIS_IS_EOS_NOTE     0x00080000  /* UCIS_COVERBIN, UCIS_ASSERTBIN */
# 
# #define UCIS_IS_FSM_RESET    0x00010000  /* UCIS_FSMBIN */
# #define UCIS_IS_FSM_TRAN     0x00020000  /* UCIS_FSMBIN */
# #define UCIS_IS_BR_ELSE      0x00010000  /* UCIS_BRANCHBIN */
# 
# #define UCIS_BIN_IFF_EXISTS  0x00010000  /* UCIS_CVGBIN UCIS_IGNOREBIN UCIS_ILLEGALBIN UCIS_DEFAULTBIN */
# #define UCIS_BIN_SAMPLE_TRUE 0x00020000  /* UCIS_CVGBIN UCIS_IGNOREBIN UCIS_ILLEGALBIN UCIS_DEFAULTBIN */
# 
# #define UCIS_IS_CROSSAUTO    0x00040000  /* UCIS_CROSS */
# 
# /* The temporary mark flag */
# #define UCIS_COVERFLAG_MARK  0x08000000  /* flag for temporary mark */
# 
# /* The reserved user flags */
# #define UCIS_USERFLAGS       0xF0000000  /* reserved for user flags */
