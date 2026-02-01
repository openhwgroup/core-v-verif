# Licensed to the Apache Software Foundation (ASF) under one
# or more contributor license agreements.  See the NOTICE file
# distributed with this work for additional information
# regarding copyright ownership.  The ASF licenses this file
# to you under the Apache License, Version 2.0 (the
# "License"); you may not use this file except in compliance
# with the License.  You may obtain a copy of the License at
#
#  http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing,
# software distributed under the License is distributed on an
# "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
# KIND, either express or implied.  See the License for the
# specific language governing permissions and limitations
# under the License.

from _io import StringIO
from ctypes import cdll, c_void_p, CFUNCTYPE
from datetime import datetime
import sys
from typing import List

from ucis import UCIS_TESTSTATUS_OK, db
import ucis
from ucis.lib.LibFactory import LibFactory
from ucis.lib.lib_ucis import LibUCIS
from ucis.mem.mem_factory import MemFactory
from ucis.report.coverage_report import CoverageReport
from ucis.report.coverage_report_builder import CoverageReportBuilder
from ucis.report.text_coverage_report_formatter import TextCoverageReportFormatter
from ucis.test_data import TestData
from ucis.ucis import UCIS
from ucis.xml.xml_factory import XmlFactory
from vsc.attrs import *
from vsc.constraints import *
from vsc.coverage import *
from vsc.methods import *
from vsc.rand_obj import *
from vsc.types import *
from vsc.visitors.coverage_save_visitor import CoverageSaveVisitor
from ucis.ucdb.ucdb_factory import UcdbFactory
from ucis.ucdb.ucdb_ucis import UcdbUCIS
from vsc import profile
from vsc.impl.ctor import glbl_debug, glbl_solvefail_debug


def get_coverage_report(details=False)->str:
    """Returns a textual coverage report of all covergroups"""
    model = get_coverage_report_model()

    out = StringIO()    
    formatter = TextCoverageReportFormatter(model, out)
    formatter.details = details
    formatter.report()
    
    return out.getvalue()

def get_coverage_report_model()->CoverageReport:
    """Returns a coverage report model of all covergroups"""
    covergroups = CoverageRegistry.inst().covergroup_types()

    db = MemFactory.create()        
    save_visitor = CoverageSaveVisitor(db)
    now = datetime.now
    save_visitor.save(TestData(
        UCIS_TESTSTATUS_OK,
        "UCIS:simulator",
        ucis.ucis_Time()), covergroups)

    return CoverageReportBuilder.build(db)    

def report_coverage(fp=None, details=False):
    """Writes a coverage report to the console"""
    if fp is None:
        fp = sys.stdout
    fp.write(get_coverage_report(details))
    
def write_coverage_db(
        filename, 
        fmt="xml",
        libucis=None):
    formats = ["xml", "libucis"]
    covergroups = CoverageRegistry.inst().covergroup_types()
    db : UCIS
    
    if fmt == "xml" or fmt == "mem":
        db = MemFactory.create()
    elif fmt == "libucis":
        if libucis is not None:
            LibFactory.load_ucis_library(libucis)
        db = LibFactory.create(None)
    else:
        raise Exception("Unsupported coverage-report format " + format 
                        + ". Supported formats: " + str(formats))
        
    save_visitor = CoverageSaveVisitor(db)
    now = datetime.now
    save_visitor.save(TestData(
        UCIS_TESTSTATUS_OK,
        "UCIS:simulator",
        ucis.ucis_Time()), covergroups)
    
    if fmt == "xml":
        XmlFactory.write(db, filename)
    elif fmt != "mem":
        db.write(filename)

    return db

def qsim_save_coverage(ucdb, region, param):
    """
    Contributes Python coverage to Mentor Questa's coverage database
    """
    
    print("ucdb=" + str(ucdb) + " region=" + str(region) + " param=" + str(param))
    # Load the UCIS library and initialize the Python
    # interface
    UcdbFactory.load_ucdb_library("libucdb.so")
    
    db = UcdbUCIS(db=ucdb)
    covergroups = CoverageRegistry.inst().covergroup_types()
    save_visitor = CoverageSaveVisitor(db)
    
    save_visitor.save(None, covergroups)
    
    pass

# Make the callback-function object global to 
# prevent it being garbage-collected
_qsim_cov_save_coverage_cb = None

def vsc_static_init():
    # Load the application
    lib = cdll.LoadLibrary(None)
    print("lib=" + str(lib))
  
    # If we're running inside Mentor QuestaSim,
    # register a callback to save coverage data 
    if hasattr(lib, "mti_AddUCDBSaveCB"):
        global _qsim_cov_save_coverage_cb
        print("PyVSC Note: Registered coverage-save callback with Mentor Questa")
        ucdb_save_func_t = CFUNCTYPE(None, c_void_p, c_void_p, c_void_p)
        add_cb = lib.mti_AddUCDBSaveCB
        add_cb.argtypes = [c_void_p, c_void_p, c_void_p]
        _qsim_cov_save_coverage_cb = ucdb_save_func_t(qsim_save_coverage)
        add_cb(None, _qsim_cov_save_coverage_cb, None)

   
#vsc_static_init()

def vsc_debug(val):
    global glbl_debug
    glbl_debug = val
    
def vsc_solvefail_debug(val):
    global glbl_solvefail_debug
    glbl_solvefail_debug = val

    
