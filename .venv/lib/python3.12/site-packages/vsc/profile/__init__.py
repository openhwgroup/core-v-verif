
import sys
import atexit
from os import environ
from vsc.profile.profiler import Profiler
from vsc.profile.solve_info import SolveInfo

_enabled = 0

def profile_on():
    global _enabled
    return _enabled > 0

def onexit():
    print("PyVSC Profile:")
    Profiler.inst().show_profile(sys.stdout)
    sys.stdout.flush()
    pass

if "VSC_PROFILE" in environ.keys() and environ["VSC_PROFILE"]:
    print("Note: profiling enabled with VSC_PROFILE")
    atexit.register(onexit)
    _enabled = 1
    
def randomize_start(srcinfo, field_model_l, constraint_l):
    global _enabled
    
    if _enabled:
        Profiler.inst().randomize_start(srcinfo, field_model_l, constraint_l)

def randomize_done(srcinfo, solve_info : SolveInfo):
    global _enabled
    if _enabled:
        Profiler.inst().randomize_done(srcinfo, solve_info)
    
    