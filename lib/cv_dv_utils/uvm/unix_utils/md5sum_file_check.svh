// ----------------------------------------------------------------------------
// Copyright 2023 CEA*
// *Commissariat a l'Energie Atomique et aux Energies Alternatives (CEA)
//
// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//    http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//[END OF HEADER]
// ----------------------------------------------------------------------------
// ----------------------------------------------------------------------------
// ----------------------------------------------------------------------------
//  Description : This file contains a task, md5sum_file_check which can be
//                used to verify that a set of files contain the correct
//                MD5SUM. For example, if there are some files that are
//                important for a simulation, but that reside outside a
//                revision control system (e.g. git), one might want to
//                ensure that a test is using the "correct" version of a
//                file by validating its md5sum.
//                
// 
// ----------------------------------------------------------------------------

// ----------------------------------------------------------------------------
// This task takes in an associative array. The keys of the associative array
//   contain file names. The contents of the array contain MD5sum values.
//
// The tasks iterates through each key in the array. It calculate the Md5sum
//   for that file and then compares that with the value provided in the
//   array. A message is printed indicated if checksums match. If the
//   flag report_error=1, then a UVM_ERROR is generated in the event of
//   a mis-match.
//
// The user may optionally provide a directory name. In this case, this
//   directory name is prefixed to each filename.
// ----------------------------------------------------------------------------
task md5sum_file_check( input string file_table[ string],    // associtive array
                        input bit    report_error = 1,
                        input string dir_prefix = ""       );

   static    string msg_prefix = "MD5SUM_CHECK";
   automatic string file_name, full_file_name;
   automatic string command_line = "";
   static    string md5sum_exec = "/usr/bin/md5sum";
   automatic string tmp_file;
   automatic int    fd,fd_uname;
   automatic string line;
   automatic string md5_back;
   automatic string msg;

   `uvm_info( msg_prefix, $sformatf("Running on server %s", hostname() ), UVM_LOW );

   // get a temporariy filename
   tmp_file = tmp_filename( .use_slash_tmp( 0 ), .prefix( "md5" ) );

   // check md5sum executable exists
   fd = $fopen( md5sum_exec, "r" );
   if (fd) begin
      $fclose(fd);
   end else begin
      `uvm_fatal( msg_prefix, $sformatf("The %0s executable is not present on %0s. Can not compute Md5sum.",
                              md5sum_exec, hostname() ) );
   end // if
               
   if ( file_table.first( file_name ) ) begin
      do begin
         // Build full file name
         if ( ( dir_prefix == "" ) ||
              ( dir_prefix.substr( dir_prefix.len()-1, dir_prefix.len()-1 ) == "/" ) ) begin
            full_file_name = { dir_prefix, file_name };            // no prefix, or prefix already end in '/'
         end else begin
            full_file_name = { dir_prefix, "/", file_name };       // need to insert "/"
         end // if

         // Check if the file in question exists
         fd = $fopen( full_file_name, "r");

         // If yes - calculate the MD5sum
         if (fd) begin
            $fclose(fd);

            // Build a command line for calling MD5sum
            command_line = $sformatf("%s %s > %s", 
                            md5sum_exec,
                            full_file_name,
                            tmp_file );
            `uvm_info( msg_prefix, $sformatf("Analyzing %0s (%0s).", 
                          full_file_name, command_line ), UVM_MEDIUM );
   
            // Call the command - which re-directs its output
            $system( command_line );
   
            // Check the output file is available
            fd = $fopen( tmp_file, "r");
            if (fd) begin
               int ret_code;

               // Read the output file
               ret_code = $fgets( line, fd );
               if ( ret_code == 0 ) begin
                  string error_string;
                  integer error_num;

                  error_num = $ferror(fd, error_string);
                  `uvm_error( msg_prefix, $sformatf("File error #%0d : %0s", error_num, error_string) );
               end // if

               // Extract the MD5sum - first 32 characters of the line
               md5_back = line.substr(0, 31);

               // Check the MD5sum matches the expected
               if ( md5_back == file_table[file_name] ) begin
                  // Case it matches
                  `uvm_info( msg_prefix, $sformatf("MD5SUM (%0s) for %0s checked OK.", md5_back, file_name ), UVM_LOW );
               end else begin
                  // If it doesn't match - either generate an info or an error
                  msg = $sformatf("MD5SUM for %0s is not correct. Wanted %0s but got %0s.",
                          file_name, file_table[file_name], md5_back );
                  if ( report_error ) begin
                    `uvm_error( msg_prefix, msg );
                  end else begin
                    `uvm_info( msg_prefix, msg, UVM_INFO );
                  end // if
               end // if
               $fclose(fd);

               // Now remove the tmp file
               rm_file( tmp_file );
            end else begin
               // Ooops - we didn't get an output file
               `uvm_error( msg_prefix, $sformatf("Unable to open %0s", tmp_file) );
            end // if
         end else begin
            `uvm_error( msg_prefix, $sformatf("Unable to open %0s", full_file_name ) );
         end // if

      end while ( file_table.next( file_name ) ) ;
   end // if first

endtask : md5sum_file_check
