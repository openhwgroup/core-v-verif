import astroid
from astroid import MANAGER

def register(linter):
    # Needed for registering the plugin.
    pass

def transform_c(cls):
    if cls.decorators is not None:
        builtins = None
        
        for d in cls.decorators.nodes:
            if isinstance(d, (astroid.Name, astroid.Call)):
                continue
            print("Attribute: " + d.attrname)
            if d.attrname == "randobj":
                builtins = ["get_model", "randomize", "randomize_with"]
                break
            elif d.attrname == "covergroup":
                builtins = ["get_model", "sample"]
                break
            elif d.attrname == "constraint":
                builtins = ["constraint_mode"]
                break
            
        if builtins is not None:
            for builtin in builtins:
                cls.locals[builtin] = [astroid.ClassDef(builtin, None)]

def transform_f(func):
#    print("Function: " + str(func.decoratornames()))
    if "constraint" in func.decoratornames():
        print("Constraint Function")
    if func.decorators is not None:
        for d in func.decorators.nodes:
            if isinstance(d, (astroid.Name, astroid.Call)):
                continue
#            print("Function Decorator: " + str(d.attrname) + " " + str(func.parent))
#            if isinstance(d, astroid.Call):
#                print("Function Decorator: " + str(d))

def _has_decorators(node):
    return node.decorators is not None
               
MANAGER.register_transform(astroid.FunctionDef, transform_f, _has_decorators) 
MANAGER.register_transform(astroid.ClassDef, transform_c, _has_decorators)
