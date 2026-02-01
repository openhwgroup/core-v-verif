'''
Created on Jun 22, 2022

@author: mballance
'''
import os
import shutil
import sys
from ucis.rgy.format_if_db import FormatIfDb
from ucis.rgy.format_if_rpt import FormatIfRpt, FormatRptOutFlags
from ucis.rgy.format_rgy import FormatRgy

def report(args):
    rgy = FormatRgy.inst()

    if args.input_format is None:
        args.input_format = rgy.getDefaultDatabase()
        
    if args.output_format is None:
        args.output_format = rgy.getDefaultReport()

    if not rgy.hasDatabaseFormat(args.input_format):
        raise Exception("Unknown input format %s ; supported=%s" % (
            args.input_format, str(rgy.getDatabaseFormats())))
    if not rgy.hasReportFormat(args.output_format):
        raise Exception("Unknown report format %s ; supported=%s" % (
            args.output_format, str(rgy.getReportFormats())))

    input_desc = rgy.getDatabaseDesc(args.input_format)
    input_if : FormatIfDb = input_desc.fmt_if()
    output_desc = rgy.getReportDesc(args.output_format)
    output_if : FormatIfRpt = output_desc.fmt_if()

    in_db = input_if.read(args.db)

    if args.out is None:
        if (output_desc.out_flags & FormatRptOutFlags.Stream) == 0:
            raise Exception("Output format %s does not support single-file output" % args.output_format)

        fp = sys.stdout
    else:
        if (output_desc.out_flags & FormatRptOutFlags.Stream) != 0:
            fp = open(args.out, "w")
        elif (output_desc.out_flags & FormatRptOutFlags.Dir) != 0:
            if os.path.exists(args.out):
                if os.path.isdir(args.out):
                    print("Note: removing existing report directory (%s)" % args.out)
                    shutil.rmtree(args.out)
                    os.makedirs(args.out)
                    fp = args.out
                else:
                    raise Exception("Output format %s requires a directory, but specified destination is a file" % (
                        args.output_format,
                        args.out
                    ))
        else:
            raise Exception("Output format %s is ambiguous about output location: %s" % (
                args.output_format,
                str(output_desc.out_flags)
            ))


    output_if.report(in_db, fp, [])

    if args.out is not None:
        fp.close()

    in_db.close()
