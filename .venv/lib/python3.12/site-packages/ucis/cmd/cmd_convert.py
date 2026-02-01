
from ucis.rgy import FormatRgy
from ucis.rgy import FormatDescDb, FormatIfDb
from ucis.merge import DbMerger

def convert(args):
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

    input_if = input_desc.fmt_if()
    output_if = output_desc.fmt_if()

    try:
        in_db = input_if.read(args.input)
    except Exception as e:
        raise Exception("Failed to read file %s ; %s" % (args.input, str(e)))

    out_db = output_if.create()

    # For now, we treat a merge like a poor-man's copy
    merger = DbMerger()
    merger.merge(out_db, [in_db])

    out_db.write(args.out)    
    in_db.close()
