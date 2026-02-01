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
Created on Jan 5, 2020

@author: ballance
'''
from ucis import UCIS
from ucis.xml.xml_writer import XmlWriter
from ucis.xml import validate_ucis_xml
from ucis.xml.xml_reader import XmlReader
import logging
class XmlFactory():
    
    @staticmethod
    def _open_file(file_path):   
        with open(file_path, 'rb') as test_f:
            magic0 = test_f.read(2)
            magic1 = test_f.read(2)
        if magic0 == b'\x1f\x8b':
            try:
                import gzip
            except ImportError:
                logging.fatal("Cannot read gzip compressed files since module gzip is not available")
            else:
                return gzip.open(file_path, 'rt')
        elif magic0 == b'\x04\x22' and magic1 == b'\x4d\x18':
            try:
                import lz4.frame
            except ImportError:
                logging.fatal("Cannot read LZ4 compressed files since module lz4.frame is not available")
            else:
                return lz4.frame.open(file_path, 'rt')
        else:
            return open(file_path, "r")

    @staticmethod
    def read(file_or_filename) -> UCIS:
        """Reads the specified XML file and returns a UCIS representation"""
        
        # First, validate the incoming XML
        if type(file_or_filename) == str:
            fp = XmlFactory._open_file(file_or_filename)
        else:
            fp = file_or_filename

        try:            
            validate_ucis_xml(fp)
        except Exception as e:
            if type(file_or_filename) == str:
                fp.close()
            raise e

        fp.seek(0)
        
        reader = XmlReader()
        
        try:
            ret = reader.read(fp)
        finally:
            if type(file_or_filename) == str:
                fp.close()

        return ret
        
    @staticmethod
    def write(db : UCIS, file_or_filename):
        """Writes the specified database in XML format"""
        writer = XmlWriter()
        
        if type(file_or_filename) == str:
            fp = open(file_or_filename, "w")
        else:
            fp = file_or_filename
        
        writer.write(fp, db)
        
        if type(file_or_filename) == str:
            fp.close()
            
