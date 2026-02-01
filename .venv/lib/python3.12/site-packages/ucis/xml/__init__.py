
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

import logging
import os
from lxml import etree
from lxml.etree import tounicode


def validate_ucis_xml(file_or_filename):
    
    xml_pkg_dir = os.path.dirname(os.path.abspath(__file__))
    schema_dir = os.path.join(xml_pkg_dir, "schema")
    ucis_xsd = os.path.join(schema_dir, "ucis.xsd")
    
    with open(ucis_xsd, "r") as xsd_fp:
        ucis_xsd_doc = etree.parse(xsd_fp)
        
#    logging.debug("schema_doc: " + tounicode(ucis_xsd_doc, pretty_print=True))
    
    ucis_schema = etree.XMLSchema(ucis_xsd_doc)
    
#    logging.debug("schema: " + str(ucis_schema))
    
    if type(file_or_filename) == str:
        logging.debug("open file")
        fp = open(file_or_filename, "r")
    else:
        fp = file_or_filename
        
    ret = False

    try:
        doc = etree.parse(fp)
        
        root = doc.getroot()

        # There is some inconsistency in whether
        # elements should be namespace-qualified or not.
        # The official schema indicates that they should be,
        # while the examples indicate they shouldn't be. The
        # (apparently) simplest way around this is to remove 
        # namespace qualification entirely.
        for elem in root.getiterator():
            if not hasattr(elem.tag, 'find'): continue  # (1)
            i = elem.tag.find('}')
            if i >= 0:
                elem.tag = elem.tag[i+1:]

        ret = ucis_schema.assertValid(doc)
        ret = True

    finally:
        if type(file_or_filename) == str:
            fp.close()

    return ret
