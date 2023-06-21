#!/usr/bin/env python3


# Copyright 2023 Silicon Labs, Inc.
#
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
#
# Licensed under the Solderpad Hardware License v 2.1 (the "License"); you may
# not use this file except in compliance with the License, or, at your option,
# the Apache License version 2.0.
#
# You may obtain a copy of the License at
# https://solderpad.org/licenses/SHL-2.1/
#
# Unless required by applicable law or agreed to in writing, any work
# distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
# WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
#
# See the License for the specific language governing permissions and
# limitations under the License.


"""
Description:
    Converts ".xlsx" to ".csv".

Rationale:
    We have vplans in ".xlsx" but that is a binary format where you can't see
    diffs when committing changes.
    Because of localization quirks (e.g. system-wide semicolon delimiter, etc),
    a script is more reliable than conversion via gui.

Usage:
    Run it on an ".xlsx" vplan.
"""


import csv
import os.path
import sys
from openpyxl import load_workbook


# Check correct usage

if len(sys.argv) != 2:
    sys.exit("usage:  {prog}  <xlsx vplan>".format(prog=sys.argv[0]))


# Read ".xlsx"

xlsx_filename = sys.argv[1]

if not os.path.isfile(xlsx_filename):
    sys.exit("error: file '{filename}' doesn't exist".format(filename=xlsx_filename))

xlsx_book = load_workbook(filename = xlsx_filename)
xlsx_sheet = xlsx_book.worksheets[0]


# Write ".csv"

csv_filename = xlsx_filename.replace(".xlsx", ".csv")
csv_file = open(csv_filename, 'w', encoding='utf-8')
csv_writer = csv.writer(csv_file)

for xlsx_row in xlsx_sheet.values:
    csv_row = []

    for xlsx_cell in xlsx_row:
        csv_cell = str(xlsx_cell or '')
        csv_row.append(csv_cell)

    csv_writer.writerow(csv_row)
