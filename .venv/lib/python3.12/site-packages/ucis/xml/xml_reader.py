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
'''
Created on Jan 6, 2020

@author: ballance
'''

from datetime import datetime
import logging
from io import StringIO
from logging import _srcfile
import sys
from typing import Dict
from xml.dom.minidom import Element

from lxml import etree
from ucis import UCIS_ENABLED_STMT, UCIS_ENABLED_BRANCH, UCIS_ENABLED_COND, \
    UCIS_ENABLED_EXPR, UCIS_ENABLED_FSM, UCIS_ENABLED_TOGGLE, UCIS_INST_ONCE, \
    UCIS_SCOPE_UNDER_DU, UCIS_DU_MODULE, UCIS_OTHER, du_scope, UCIS_INSTANCE,\
    UCIS_CVGBIN, UCIS_IGNOREBIN, UCIS_ILLEGALBIN
from ucis.mem.mem_file_handle import MemFileHandle
from ucis.mem.mem_scope import MemScope
from ucis.mem.mem_ucis import MemUCIS
from ucis.statement_id import StatementId
from ucis.ucis import UCIS
from ucis.xml import validate_ucis_xml


class XmlReader():
    
    def __init__(self):
        self.file_m : Dict[int,MemFileHandle] = {}
        self.module_scope_m : Dict[str, MemScope] = {}
        self.inst_scope_m : Dict[str, MemScope] = {}
        pass

    def loads(self, s) -> UCIS:
        fp = StringIO(s)
        return self.read(fp)


    def read(self, file) -> UCIS:
        tree = etree.parse(file)
        root = tree.getroot()
        self.db = MemUCIS()
        
        for elem in root.getiterator():
            if not hasattr(elem.tag, 'find'): continue  # (1)
            i = elem.tag.find('}')
            if i >= 0:
                elem.tag = elem.tag[i+1:]
       
#        self.db.setWrittenBy(root.get("writtenBy"))
#        self.db.setWrittenTime(self.getAttrDateTime(root, "writtenTime"))
        
        for srcFileN in tree.iter("sourceFiles"):
            self.readSourceFile(srcFileN)
            
        for histN in tree.iter("historyNodes"):
            self.readHistoryNode(histN)

        for instN in tree.iter("instanceCoverages"):
            self.readInstanceCoverage(instN)
            
        return self.db
    
    @staticmethod
    def validate(file_or_filename):
        validate_ucis_xml(file_or_filename)
        
    
    def readSourceFile(self, srcFileN):
        filename = srcFileN.get("fileName")
        id = int(srcFileN.get("id"))
        file_h = self.db.createFileHandle(filename, None)
        self.file_m[id] = file_h
        
        return file_h
    
    def readHistoryNode(self, histN):
        parent = None
        logicalname = histN.get("logicalName")
        physicalname = self.getAttr(histN, "physicalName", None)
        kind = self.getAttr(histN, "kind", None)
        
        ret = self.db.createHistoryNode(parent, logicalname, physicalname, kind)
        ret.setTestStatus(self.getAttrBool(histN, "testStatus"))
        self.setFloatIfEx(histN, ret.setSimTime, "simtime")
        self.setIfEx(histN, ret.setTimeUnit, "timeunit")
        self.setIfEx(histN, ret.setRunCwd, "runCwd")
        self.setFloatIfEx(histN, ret.setCpuTime, "cpuTime")
        self.setIfEx(histN, ret.setSeed, "seed")
        self.setIfEx(histN, ret.setCmd, "cmd")
        self.setIfEx(histN, ret.setArgs, "args")
        self.setIfEx(histN, ret.setCompulsory, "compulsory")
        ret.setDate(self.getAttrDateTime(histN, "date"))
        self.setIfEx(histN, ret.setUserName, "userName")
        self.setFloatIfEx(histN, ret.setCost, "cost")
        ret.setToolCategory(histN.attrib["toolCategory"])
        ret.setVendorId(histN.attrib["vendorId"])
        ret.setVendorTool(histN.attrib["vendorTool"])
        ret.setVendorToolVersion(histN.attrib["vendorToolVersion"])
        self.setIntIfEx(histN, ret.setSameTests, "sameTests")
        self.setIfEx(histN, ret.setComment, "comment")
        
        return ret
    
    def readInstanceCoverage(self, instN):
        name = instN.attrib["name"]
        stmt_id = None
        for stmt_idN in instN.iter("id"):
            stmt_id = self.readStatementId(stmt_idN)
            
        srcinfo = None
            
        # TODO: Creating a coverage instance depends on
        # having a du_type
        module_scope_name = self.getAttr(instN, "moduleName", "default")
        
        type_scope = self.getScope(
            module_scope_name, 
            None, 
            UCIS_OTHER) # TODO: how do we determine source type?
        
        inst_scope = self.getInstScope(
            name,
            srcinfo,
            UCIS_OTHER,
            type_scope)
        
        for cg in instN.iter("covergroupCoverage"):
            self.readCovergroups(cg, inst_scope, module_scope_name)

#        self.setIntIfEx(instN, ret.setAli, name)

    def readCovergroups(self, cg, inst_scope, module_scope_name):
        # This entry is for a given covergroup type
        
        cg_typescope = None
        covergroup_scope = None

        # The name attribute associated with each cgInstance is the
        # covergroup instance name. The type name is stored in the 
        # cgId entity / cgName attribute

        cg_type_m = {}

        instances = [i for i in cg.iter("cgInstance")]

        for i in cg.iter("cgInstance"):
            try:
                cgId_l = next(i.iter("cgId"))
                typename = self.getAttr(cgId_l, "cgName", "xxx")
            except:
                typename = "default"

            if typename in cg_type_m.keys():
                cg_type_m[typename].append(i)
            else:
                cg_type_m[typename] = [i]

        # UCIS XML coverage data only has instance information.
        # The reader is responsible for reconstructing the 
        # type coverage information
        for cg_typename in cg_type_m.keys():
            cg_typescope = inst_scope.createCovergroup(
                cg_typename,
                None,
                1,
                UCIS_OTHER)

            # Process all instances of a given covergroup type
            self.readCovergroup(cg_typescope, cg_type_m[cg_typename])

    def readCovergroup(self, cg_t, cg_l):

        cr_m = {}
        cp_m = {}

        # Create a merged understanding of all covergroup instances
        cg_inst_l = []
        for cg_e in cg_l:
            srcinfo = None

            cg_i_name = self.getAttr(cg_e, "name", "<unknown>")
            cg_i = cg_t.createCoverInstance(
                cg_i_name, 
                srcinfo,
                1,
                UCIS_OTHER)

            # Build up a map of coverpoint name/inst-handle refs
            cg_inst_cp_m = {}

            for cp_e in cg_e.iter("coverpoint"):
                cp_name = self.getAttr(cp_e, "name", "<unknown>")

                if cp_name not in cp_m.keys():
                    # New coverpoint. Create type and instance
                    # representations
                    cp_t = cg_t.createCoverpoint(
                        cp_name,
                        srcinfo,
                        1,
                        UCIS_OTHER)

                    # Tuple of coverpoint type and map between
                    # bin name and count
                    cp_i = (cp_t, {})
                    cp_m[cp_name] = cp_i
                else:
                    # Already-known coverpoint. Only create
                    # new instance representation
                    cp_i = cp_m[cp_name]

                cp_inst = self.readCoverpointInst(cg_i, cp_e, cp_i)
                cg_inst_cp_m[cp_name] = cp_inst

            for cr_e in cg_e.iter("cross"):
                cp_name = self.getAttr(cr_e, "name", "<unknown>")

                if cp_name not in cr_m.keys():
                    cp_l = []
                    for crossExpr in cr_e.iter("crossExpr"):
                        cp_n = crossExpr.text.strip()
                        logging.debug("cp_n=\"" + cp_n + "\"")
                        if cp_n in cp_m.keys():
                            cp_l.append(cp_m[cp_n][0])
                        else:
                            raise Exception("Cross %s references missing coverpoint %s" % (
                                cp_name, cp_n))

                    # New crosspoint
                    cr_t = cg_t.createCross(
                        cp_name,
                        srcinfo,
                        1,
                        UCIS_OTHER,
                        cp_l)

                    cr_i = (cr_t, {})
                    cr_m[cp_name] = cr_i
                else:
                    # Already-known crosspoint. Only create
                    # new instance representation
                    cr_i = cr_m[cp_name]
                
                self.readCrossInst(cg_i, cr_e, cr_i, cg_inst_cp_m)

        # Now, create the type info
        for cp_name in cp_m.keys():
            self.populateCoverpointType(cp_m[cp_name][0], cp_m[cp_name][1])

        # Now, create the cross type info
        for cr_name in cr_m.keys():
            self.populateCrossType(
                cr_m[cr_name][0],
                cr_m[cr_name][1])

        pass
                
    def readCoverpointInst(self, cg_i, cp_e, cp_type_i):
        srcinfo = None
        
        cp = cg_i.createCoverpoint(
            self.getAttr(cp_e, "name", "<unknown>"),
            srcinfo,
            1, # weight
            UCIS_OTHER)
        
        for cpBin in cp_e.iter("coverpointBin"):
            self.readCoverpointBin(cpBin, cp, cp_type_i)
            
        return cp
            
    def readCoverpointBin(self, cpBin : Element, cp, cp_type_i):
        srcinfo = None

        seq = next(cpBin.iter("sequence"),None)
        rng = next(cpBin.iter("range"),None)

        if seq is not None:
            contents = next(seq.iter("contents"))
        elif rng is not None:
            contents = next(rng.iter("contents"))
        else:
            raise Exception("Format error: neither 'sequence' nor 'range' present")

        kind_a = self.getAttr(cpBin, "type", "default")
        kind = UCIS_CVGBIN
        
        if kind_a == "bins" or kind_a == "default":
            kind = UCIS_CVGBIN
        elif kind_a == "ignore":
            kind = UCIS_IGNOREBIN
        elif kind_a == "illegal":
            kind = UCIS_ILLEGALBIN
        else:
            raise Exception("Unknown bin type %s" % str(kind_a))
        
        cp_bin_name = self.getAttr(cpBin, "name", "<unknown>")
        cp_bin_count = self.getAttrInt(contents, "coverageCount")

        if cp_bin_name not in cp_type_i[1].keys():
            cp_type_i[1][cp_bin_name] = (kind, cp_bin_count)
        else:
            entry = cp_type_i[1][cp_bin_name]
            cp_type_i[1][cp_bin_name] = (entry[0], entry[1] + cp_bin_count)
        
        cp.createBin(
            cp_bin_name,
            srcinfo,
            1,
            cp_bin_count,
            self.getAttr(cpBin, "name", "default"),
            kind)
        
    def populateCoverpointType(self, cp_t, cp_bin_m):
        srcinfo = None

        for bin_name,(kind,count) in cp_bin_m.items():
            cp_t.createBin(
                bin_name,
                srcinfo,
                1,
                count,
                bin_name,
                kind)

    def readCrossInst(self, cg_i, cr_e, cr_type_i, cp_m):
        name = self.getAttr(cr_e, "name", "<unknown>")
        
        cp_l = []
        for crossExpr in cr_e.iter("crossExpr"):
            cp_n = crossExpr.text.strip()
            logging.debug("cp_n=\"" + cp_n + "\"")
            if cp_n in cp_m.keys():
                cp_l.append(cp_m[cp_n])
            else:
                raise Exception("Cross " + cp_n + " references missing coverpoint " + cp_n)

        srcinfo = None
        
        cr = cg_i.createCross(
            name,
            srcinfo,
            1, # weight
            UCIS_OTHER,
            cp_l)
        
        for crb_e in cr_e.iter("crossBin"):
            self.readCrossBin(crb_e, cr, cr_type_i)
        
        return cr

    def populateCrossType(self, cr_t, cr_bin_m):
        srcinfo = None

        for bin_name,count in cr_bin_m.items():
            cr_t.createBin
            cr_t.createBin(
                bin_name,
                srcinfo,
                1, # weight
                count,
                "") # TODO:
        pass
    
    def readCrossBin(self, crb_e, cr, cr_type_i):
        name = self.getAttr(crb_e, "name", "default")
        srcinfo = None
        contentsN = next(crb_e.iter("contents"))

        count = self.getAttrInt(contentsN, "coverageCount")

        if name in cr_type_i[1].keys():
            cr_type_i[1][name] += count
        else:
            cr_type_i[1][name] = count

        cr.createBin(
            name,
            srcinfo,
            1, # weight
            count,
            "") # TODO:

        

    def readStatementId(self, stmt_idN):
        file_id = int(stmt_idN.attrib["file"])
        line = int(stmt_idN.attrib["line"])
        item = int(stmt_idN.attrib["inlineCount"])
        file = self.file_m[file_id]
        return StatementId(file, line, item)

    def getScope(self,
                 name,
                 srcinfo,
                 source):
        
        if name not in self.module_scope_m.keys():
            scope = self.db.createScope(
                name, 
                srcinfo, 
                1, 
                source, 
                UCIS_DU_MODULE,
                UCIS_ENABLED_STMT | UCIS_ENABLED_BRANCH
                | UCIS_ENABLED_COND | UCIS_ENABLED_EXPR
                | UCIS_ENABLED_FSM | UCIS_ENABLED_TOGGLE
                | UCIS_INST_ONCE | UCIS_SCOPE_UNDER_DU)
            self.module_scope_m[name] = scope
        else:
            scope = self.module_scope_m[name]
            
        return scope
    
    def getInstScope(self,
                     name,
                     srcinfo,
                     source,
                     du_scope):
        if name not in self.inst_scope_m.keys():
            scope = self.db.createInstance(
                name,
                srcinfo,
                1,
                source,
                UCIS_INSTANCE,
                du_scope,
                UCIS_INST_ONCE)
            self.inst_scope_m[name] = scope
        else:
            scope = self.inst_scope_m[name]
            
        return scope
    
    def getAttrDateTime(self, e, name):
        """Converts ISO time used by XML to the YYYYMMDDHHMMSS format used by the library"""
        val = e.get(name)
        dateVal = datetime.strptime(val,"%Y-%m-%dT%H:%M:%S")
        return dateVal.strftime("%Y%m%d%H%M%S")
    
    def getAttr(self, node, name, default):
        if name in node.attrib:
            return node.attrib[name]
        else:
            return default
        
    def getAttrBool(self, e, name):
        if e.attrib[name] == "true":
            return True
        else:
            return False
        
    def getAttrInt(self, e, name):
        return int(e.attrib[name])
        
    def setIfEx(self, n, f, name):
        if name in n.attrib:
            f(n.attrib[name])
            
    def setIntIfEx(self, n, f, name):
        if name in n.attrib:
            f(int(n.attrib[name]))

    def setFloatIfEx(self, n, f, name):
        if name in n.attrib:
            f(float(n.attrib[name]))
