'''
Created on Jun 22, 2022

@author: mballance
'''
from ucis.rgy.format_rgy import FormatRgy

def list_report_formats(args):
    rgy = FormatRgy.inst()
    
    fmts = rgy.getReportFormats()
    
    max_w = 0
    for fmt in fmts:
        if len(fmt) > max_w:
            max_w = len(fmt)
        
    for fmt in fmts:
        desc = rgy.getReportDesc(fmt)
        text = fmt
        if len(fmt) < max_w:
            text += ' '*(max_w-len(fmt))
        text += " - %s" % desc.description
        
        print(text)
    