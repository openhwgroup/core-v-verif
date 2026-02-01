'''
Created on Jun 11, 2022

@author: mballance
'''
import argparse
from ucis.cmd import cmd_list_db_formats
from ucis.cmd import cmd_list_report_formats
from ucis.cmd import cmd_report, cmd_merge, cmd_convert
import sys
import traceback

def get_parser():
    parser = argparse.ArgumentParser(description="Manipulate UCIS coverage data")
    parser.prog = "ucis"
    
    subparser = parser.add_subparsers()
    subparser.required = True

    convert = subparser.add_parser("convert",
        help="""
        Converts coverage data from one format to another
        """)
    convert.add_argument("--out", "-o",
        help="Specifies the output of the conversion",
        required=True)
    convert.add_argument("--input-format", "-if",
        help="Specifies the format of the input database. Defaults to 'xml'")
    convert.add_argument("--output-format", "-of",
        help="Specifies the format of the output database. Defaults to 'xml'")
    convert.add_argument("input", help="Source database to convert")
    convert.set_defaults(func=cmd_convert.convert)
   
    merge = subparser.add_parser("merge",
        help="""
        Merges coverage data from two or more databases into a single merged database
        """)
    merge.add_argument("--out", "-o", 
        help="Specifies the output of the merge",
        required=True)
    merge.add_argument("--input-format", "-if",
        help="Specifies the format of the input databases. Defaults to 'xml'")
    merge.add_argument("--output-format", "-of",
        help="Specifies the format of the input databases. Defaults to 'xml'")
    merge.add_argument("--libucis", "-l",
        help="Specifies the name/path of the UCIS shared library")
    merge.add_argument("db", nargs="+")
    merge.set_defaults(func=cmd_merge.merge)
    
    list_db_formats = subparser.add_parser("list-db-formats",
        help="Shows available database formats")
    list_db_formats.set_defaults(func=cmd_list_db_formats.list_db_formats)
    
    list_rpt_formats = subparser.add_parser("list-rpt-formats",
        help="Shows available report filters")
    list_rpt_formats.set_defaults(func=cmd_list_report_formats.list_report_formats)
    
    report = subparser.add_parser("report",
        help="Generate a report (typically textual) from coverage data")
    report.add_argument("--out", "-o",
        help="Specifies the output location for the report")
    report.add_argument("--input-format", "-if",
        help="Specifies the format of the input database. Defaults to 'xml'")
    report.add_argument("--output-format", "-of",
        help="Specifies the output format of the report. Defaults to 'txt'")
    report.add_argument("db", help="Path to the coverage database")
    report.set_defaults(func=cmd_report.report)

    
    return parser

def main():
    parser = get_parser()

    argv = []
    plusargs = []
    for arg in sys.argv[1:]:
        if arg[0] == '+':
            plusargs.append(arg)
        else:
            argv.append(arg)

    args = parser.parse_args(args=argv)
    setattr(args, "plusargs", plusargs)

    try:
        args.func(args)
    except Exception as e:
        traceback.print_exc()
        print("Error: %s" % "{0}".format(e))

if __name__ == "__main__":
    main()
    
