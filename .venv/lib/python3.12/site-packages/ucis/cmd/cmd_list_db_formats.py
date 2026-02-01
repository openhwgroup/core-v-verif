'''
Created on Jun 22, 2022

@author: mballance
'''
from ucis.rgy.format_rgy import FormatRgy


def list_db_formats(args):
    rgy = FormatRgy.inst()

    fmts = rgy.getDatabaseFormats()
    max_w = 0
    for fmt in fmts:
        if len(fmt) > max_w:
            max_w = len(fmt)

    for fmt in fmts:
        desc = rgy.getDatabaseDesc(fmt)
        text = fmt
        if len(fmt) < max_w:
            text += ' '*(max_w-len(fmt))
        text += " - %s" % desc.description
        print(text)
    pass