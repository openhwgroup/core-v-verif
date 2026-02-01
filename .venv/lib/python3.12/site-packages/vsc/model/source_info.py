import inspect


# Created on Mar 13, 2020
#
# @author: ballance


class SourceInfo(object):
    
    def __init__(self, filename, lineno):
        self.filename = filename
        self.lineno = lineno
        
    def __str__(self):
        return self.filename + ":" + str(self.lineno)
    
    def clone(self):
        return SourceInfo(self.filename, self.lineno)
    
    @classmethod
    def mk(cls, levels=1):
        stack = inspect.stack()
       
        if len(stack) <= (levels+1):
            raise Exception("requested stack frame %d out-of-bounds (%d)" % (
                levels, len(stack)))
        frame = inspect.stack()[levels+1]
        
        return cls(frame.filename, frame.lineno)
    
    @staticmethod
    def toString(srcinfo):
        if srcinfo is not None:
            return "%s:%d" % (srcinfo.filename, srcinfo.lineno)
        else:
            return "<unknown>"
        
