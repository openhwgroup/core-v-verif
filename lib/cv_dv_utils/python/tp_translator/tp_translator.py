# ----------------------------------------------------------------------------
# Copyright 2024 CEA*
# *Commissariat a l'Energie Atomique et aux Energies Alternatives (CEA)
#
# SPDX-License-Identifier: Apache-2.0
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#    http://www.apache.org/licenses/LICENSE-2.0
#
##[END OF HEADER]
# ----------------------------------------------------------------------------
import pandas as pd
import argparse

parser = argparse.ArgumentParser(description='Input/Output options')
parser.add_argument('--xls_in', dest='input_xls', type=str, help='Name of input xls file')
parser.add_argument('--xls_out', dest='output_xls', type=str, help='Name of output xls file')

args = parser.parse_args()


## Read Mapping Sheet
df_mapping    = pd.read_excel(args.input_xls, sheet_name=2, dtype={'Features': str, 'Test Items': str})
df_features   = pd.read_excel(args.input_xls, sheet_name=0)
df_test_items = pd.read_excel(args.input_xls, sheet_name=1, skiprows=2, dtype={'Section': str, 'Title': str, 'Description': str})

#print(df_mapping)
top_dict = [];
#for i, row in df_mapping.iterrows():
#    top_dict.append({'Feature ID'          : row.iloc[0],
#                     'Feature'             : df_features[df_features['Sub Section']==row.iloc[0]].iloc[0]['Feature'], 
#                     'Sub feature'         : df_features[df_features['Sub Section']==row.iloc[0]].iloc[0]['Sub Feature'], 
#                     'Test Items Title'    : df_test_items[df_test_items['Section']==row.iloc[1]].iloc[0]['Title'],
#                     'Verification Goal'   : df_test_items[df_test_items['Section']==row.iloc[1]].iloc[0]['Description'],
#                     'Criteria Pass Fail'  : df_test_items[df_test_items['Section']==row.iloc[1]].iloc[0]['Criteria Pass Fail'],
#                     'Type'                : df_test_items[df_test_items['Section']==row.iloc[1]].iloc[0]['Type'],
#                     })
#
for i, row in df_mapping.iterrows():
#    print(row.iloc[0], row.iloc[1])
    top_dict.append({'Requirement ID'      : df_features[df_features['Sub Section']==row.iloc[0]].iloc[0]['Section'],
                     'Feature'             : df_features[df_features['Sub Section']==row.iloc[0]].iloc[0]['Feature'], 
                     'Sub Feature'         : df_features[df_features['Sub Section']==row.iloc[0]].iloc[0]['Sub Feature'], 
                     'Feature Description' : df_features[df_features['Sub Section']==row.iloc[0]].iloc[0]['Feature'], 
                     'Test Case'           : df_test_items[df_test_items['Section']==row.iloc[1]].iloc[0]['Title'],
                     'Verification Goal'   : df_test_items[df_test_items['Section']==row.iloc[1]].iloc[0]['Description'],
                     'Criteria Pass Fail'  : df_test_items[df_test_items['Section']==row.iloc[1]].iloc[0]['Criteria Pass Fail'],
                     'Test Type'           : df_test_items[df_test_items['Section']==row.iloc[1]].iloc[0]['Test Type'],
                     'Coverage Method'     : df_test_items[df_test_items['Section']==row.iloc[1]].iloc[0]['Coverage Method'],
                     'link To Coverage'    : "",
                     })


## Create a Pandas Excel writer using XlsxWriter as the engine.
writer = pd.ExcelWriter(args.output_xls, engine='xlsxwriter')

# Convert the dataframe to an XlsxWriter Excel object. Note that we turn off
# the default header and skip one row to allow us to insert a user defined
# header.
df = pd.DataFrame(top_dict)

# remove cells which are duplicated
# Shift gives the previous cell
df['Feature']        = df['Feature'].mask(df['Feature'].eq(df['Feature'].shift()))
df['Feature Description']        = df['Feature Description'].mask(df['Feature Description'].eq(df['Feature Description'].shift()))
df['Requirement ID'] = df['Requirement ID'].mask(df['Requirement ID'].eq(df['Requirement ID'].shift()))
#df['Sub Feature ID'] = df['Sub Feature ID'].mask(df['Sub Feature ID'].eq(df['Sub Feature ID'].shift()))
df['Sub Feature']    = df['Sub Feature'].mask(df['Sub Feature'].eq(df['Sub Feature'].shift()))

#for i, row in df_test_items.iterrows():
#  if  row.iloc[1] not in df_mapping.values:
#    if pd.isnull(row['Coverage Method']) == False:
#        top_dict.append({'Requirement ID'      : 'NA',
#                         'Feature'             : 'Verification Items', 
#                         'Sub Feature'         : 'Verification Items', 
#                         'Feature Description' : 'Verification Items', 
#                         'Test Case'           : row['Title'],
#                         'Verification Goal'   : row['Description'],
#                         'Criteria Pass Fail'  : row['Criteria Pass Fail'],
#                         'Test Type'           : row['Test Type'],
#                         'Coverage Method'     : row['Coverage Method'],
#                         })
#df = pd.DataFrame(top_dict)

# Convert the dataframe to an XlsxWriter Excel object. Note that we turn off
# the default header and skip one row to allow us to insert a user defined
# header.
df.to_excel(writer, sheet_name="Test Items", startrow=1, startcol=0, header=False, index=False)

# Get the xlsxwriter workbook and worksheet objects.
workbook  = writer.book
worksheet = writer.sheets["Test Items"]

# Add a header format.
header_format = workbook.add_format(
    {
        "bold": True,
        "text_wrap": True,
        "valign": "top",
        "fg_color": "#D7E4BC",
        "border": 1,
    }
)
# format the columns
col_1st    = writer.book.add_format({'bold':True, 'border': 1})
col_others = writer.book.add_format({'bold':False, 'text_wrap': True, 'border': 1})

# Write the column headers with the defined format.
for col_num, value in enumerate(df.columns.values):
    worksheet.write(0, col_num, value, header_format)


#col_1st.set_bg_color('#CAF5FF')

worksheet.set_column(0,9,80,col_others)
worksheet.set_column(0,0,20,col_1st)
#worksheet.set_column(2,2,10,col_1st)

# Close the Pandas Excel writer and output the Excel file.


writer.close()

