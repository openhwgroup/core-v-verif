'''
Created on Jun 11, 2022

@author: mballance
'''

from typing import List
from ucis.merge.db_merger import DbMerger
from ucis.rgy import FormatRgy
from ucis.rgy.format_if_db import FormatDescDb, FormatIfDb
from ucis.ucis import UCIS

def merge(args):
    if args.input_format is None:
        args.input_format = "xml"
    if args.output_format is None:
        args.output_format = "xml"

    rgy = FormatRgy.inst()
    if not rgy.hasDatabaseFormat(args.input_format):
        raise Exception("Input format %s not recognized" % args.input_format)
    if not rgy.hasDatabaseFormat(args.output_format):
        raise Exception("Output format %s not recognized" % args.output_format)

    input_desc : FormatDescDb = rgy.getDatabaseDesc(args.input_format)
    output_desc : FormatDescDb = rgy.getDatabaseDesc(args.output_format)

    db_l : List[UCIS] = []
    for input in args.db:
        db_if : FormatIfDb = input_desc.fmt_if()
        try:
            db = db_if.read(input)
            db_l.append(db)
        except Exception as e:
            raise Exception("Failed to read input file %s: %s" % (
                input,
                str(e)
            ))

    out_if = output_desc.fmt_if()
    out_db : UCIS = out_if.create() 

    merger = DbMerger()
    try:
        merger.merge(out_db, db_l)
    except Exception as e:
        raise Exception("Merge operation failed: %s" % str(e))
    
    out_db.write(args.out)
    for db in db_l:
        db.close()

    
