//----------------------------------------------------------------------
// Copyright 2007-2009 Mentor Graphics Corporation
// Copyright 2007-2018 Cadence Design Systems, Inc.
// Copyright 2018 NVIDIA Corporation
//   All Rights Reserved Worldwide
//
//   Licensed under the Apache License, Version 2.0 (the
//   "License"); you may not use this file except in
//   compliance with the License.  You may obtain a copy of
//   the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
//   Unless required by applicable law or agreed to in
//   writing, software distributed under the License is
//   distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//   CONDITIONS OF ANY KIND, either express or implied.  See
//   the License for the specific language governing
//   permissions and limitations under the License.
//----------------------------------------------------------------------

//------------------------------------------------------------------------------
// Group -- NODOCS -- Recording Macros
//
// The recording macros assist users who implement the <uvm_object::do_record>
// method. They help ensure that the fields are recorded using a vendor-
// independent API. Unlike the <uvm_recorder> policy, fields recorded using
// the macros do not lose type information--they are passed
// directly to the vendor-specific API. This results in more efficient recording
// and no artificial limit on bit-widths. See your simulator vendor's 
// documentation for more information on its transaction recording capabilities.
//------------------------------------------------------------------------------

`ifndef UVM_RECORDER_DEFINES_SVH
`define UVM_RECORDER_DEFINES_SVH

// Macro -- NODOCS -- `uvm_record_attribute
//
// Vendor-independent macro to hide tool-specific interface for
// recording attributes (fields) to a transaction database.
//
//| `uvm_record_attribute(TR_HANDLE, NAME, VALUE)
//
// The default implementation of the macro passes ~NAME~ and
// ~VALUE~ through to the <uvm_recorder::record_generic> method.
//
// This macro should not be called directly by the user, the
// other recording macros will call it automatically if 
// <uvm_recorder::use_record_attribute> returns true.
//

`ifndef uvm_record_attribute
 `ifdef QUESTA
    `define uvm_record_attribute(TR_HANDLE,NAME,VALUE) \
      $add_attribute(TR_HANDLE,VALUE,NAME);
  `else
    // @uvm-ieee 1800.2-2017 auto B.2.3.1
    `define uvm_record_attribute(TR_HANDLE,NAME,VALUE) \
      recorder.record_generic(NAME, $sformatf("%p", VALUE)); 
  `endif
`endif

// Macro -- NODOCS -- `uvm_record_int
//
//| `uvm_record_int(NAME,VALUE,SIZE[,RADIX])
//
// The ~`uvm_record_int~ macro takes the same arguments as
// the <uvm_recorder::record_field> method (including the optional ~RADIX~).
//
// The default implementation will pass the name/value pair to
// <`uvm_record_attribute> if enabled, otherwise the information
// will be passed to <uvm_recorder::record_field>.
//

`ifndef uvm_record_int
  // @uvm-ieee 1800.2-2017 auto B.2.3.2
  `define uvm_record_int(NAME,VALUE,SIZE,RADIX = UVM_NORADIX) \
    if (recorder != null && recorder.is_open()) begin \
      if (recorder.use_record_attribute()) \
        `uvm_record_attribute(recorder.get_record_attribute_handle(),NAME,VALUE) \
      else \
        if (SIZE > 64) \
          recorder.record_field(NAME, VALUE, SIZE, RADIX); \
        else \
          recorder.record_field_int(NAME, VALUE, SIZE, RADIX); \
    end
`endif

// Macro -- NODOCS -- `uvm_record_string
//
//| `uvm_record_string(NAME,VALUE)
//
// The ~`uvm_record_string~ macro takes the same arguments as
// the <uvm_recorder::record_string> method.
//
// The default implementation will pass the name/value pair to
// <`uvm_record_attribute> if enabled, otherwise the information
// will be passed to <uvm_recorder::record_string>.
//

`ifndef uvm_record_string
  // @uvm-ieee 1800.2-2017 auto B.2.3.3
  `define uvm_record_string(NAME,VALUE) \
    if (recorder != null && recorder.is_open()) begin \
      if (recorder.use_record_attribute()) \
        `uvm_record_attribute(recorder.get_record_attribute_handle(),NAME,VALUE) \
      else \
        recorder.record_string(NAME,VALUE); \
    end
`endif

// Macro -- NODOCS -- `uvm_record_time
//
//| `uvm_record_time(NAME,VALUE)
//
// The ~`uvm_record_time~ macro takes the same arguments as
// the <uvm_recorder::record_time> method.
//
// The default implementation will pass the name/value pair to
// <`uvm_record_attribute> if enabled, otherwise the information
// will be passed to <uvm_recorder::record_time>.
//
`ifndef uvm_record_time
  // @uvm-ieee 1800.2-2017 auto B.2.3.4
  `define uvm_record_time(NAME,VALUE) \
    if (recorder != null && recorder.is_open()) begin \
      if (recorder.use_record_attribute()) \
        `uvm_record_attribute(recorder.get_record_attribute_handle(),NAME,VALUE) \
      else \
         recorder.record_time(NAME,VALUE); \
    end
`endif


// Macro -- NODOCS -- `uvm_record_real
//
//| `uvm_record_real(NAME,VALUE)
//
// The ~`uvm_record_real~ macro takes the same arguments as
// the <uvm_recorder::record_field_real> method.
//
// The default implementation will pass the name/value pair to
// <`uvm_record_attribute> if enabled, otherwise the information
// will be passed to <uvm_recorder::record_field_real>.
//
`ifndef uvm_record_real
  // @uvm-ieee 1800.2-2017 auto B.2.3.5
  `define uvm_record_real(NAME,VALUE) \
    if (recorder != null && recorder.is_open()) begin \
      if (recorder.use_record_attribute()) \
        `uvm_record_attribute(recorder.get_record_attribute_handle(),NAME,VALUE) \
      else \
        recorder.record_field_real(NAME,VALUE); \
    end
`endif

// @uvm-ieee 1800.2-2017 auto B.2.3.6
`define uvm_record_field(NAME,VALUE) \
   if (recorder != null && recorder.is_open()) begin \
     if (recorder.use_record_attribute()) begin \
       `uvm_record_attribute(recorder.get_record_attribute_handle(),NAME,VALUE) \
     end \
     else \
       recorder.record_generic(NAME, $sformatf("%p", VALUE)); \
   end

`define uvm_record_enum(NAME,VALUE,TYPE) \
  if (recorder != null && recorder.is_open()) begin \
    if (recorder.use_record_attribute()) begin \
       `uvm_record_attribute(recorder.get_record_attribute_handle(),NAME,VALUE) \
    end \
    else begin \
      if (VALUE.name() == "") \
        recorder.record_generic(NAME, $sformatf("%0d", VALUE), `"TYPE`"); \
      else \
        recorder.record_generic(NAME, VALUE.name(), `"TYPE`"); \
    end \
 end

// uvm_record_qda_int
// ------------------

`define uvm_record_qda_int(ARG, RADIX) \
  begin \
    int sz__ = $size(ARG); \
    if(sz__ == 0) begin \
      `uvm_record_int(`"ARG`", 0, 32, UVM_DEC) \
    end \
    else if(sz__ < 10) begin \
      foreach(ARG[i]) begin \
        string nm__ = $sformatf("%s[%0d]", `"ARG`", i); \
        `uvm_record_int(nm__, ARG[i], $bits(ARG[i]), RADIX) \
      end \
    end \
    else begin \
      for(int i=0; i<5; ++i) begin \
        string nm__ = $sformatf("%s[%0d]", `"ARG`", i); \
        `uvm_record_int(nm__, ARG[i], $bits(ARG[i]), RADIX) \
      end \
      for(int i=sz__-5; i<sz__; ++i) begin \
        string nm__ = $sformatf("%s[%0d]", `"ARG`", i); \
        `uvm_record_int(nm__, ARG[i], $bits(ARG[i]), RADIX) \
      end \
    end \
  end 

// uvm_record_qda_object
// ---------------------

`define uvm_record_qda_object(ARG) \
  begin \
    int sz__ = $size(ARG); \
    if(sz__ == 0) begin \
      `uvm_record_int(`"ARG`", 0, 32, UVM_DEC) \
    end \
    else if(sz__ < 10) begin \
      foreach(ARG[i]) begin \
        string nm__ = $sformatf("%s[%0d]", `"ARG`", i); \
        recorder.record_object(nm__, ARG[i]); \
      end \
    end \
    else begin \
      for(int i=0; i<5; ++i) begin \
        string nm__ = $sformatf("%s[%0d]", `"ARG`", i); \
        recorder.record_object(nm__, ARG[i]); \
      end \
      for(int i=sz__-5; i<sz__; ++i) begin \
        string nm__ = $sformatf("%s[%0d]", `"ARG`", i); \
        recorder.record_object(nm__, ARG[i]); \
      end \
    end \
  end

// uvm_record_qda_enum
// --------------------

`define uvm_record_qda_enum(ARG, T) \
  begin \
    int sz__ = $size(ARG); \
    if(sz__ == 0) begin \
      `uvm_record_int(`"ARG`", 0, 32, UVM_DEC) \
    end \
    else if(sz__ < 10) begin \
      foreach(ARG[i]) begin \
        string nm__ = $sformatf("%s[%0d]", `"ARG`", i); \
        `uvm_record_enum(nm__, ARG[i], T) \
      end \
    end \
    else begin \
      for(int i=0; i<5; ++i) begin \
        string nm__ = $sformatf("%s[%0d]", `"ARG`", i); \
        `uvm_record_enum(nm__, ARG[i], T) \
      end \
      for(int i=sz__-5; i<sz__; ++i) begin \
        string nm__ = $sformatf("%s[%0d]", `"ARG`", i); \
        `uvm_record_enum(nm__, ARG[i], T) \
      end \
    end \
  end

// uvm_record_qda_string
// ---------------------

`define uvm_record_qda_string(ARG) \
  begin \
    int sz__; \
    /* workaround for sarray string + $size */ \
    foreach (ARG[i]) \
      sz__ = i; \
    if(sz__ == 0) begin \
      `uvm_record_int(`"ARG`", 0, 32, UVM_DEC) \
    end \
    else if(sz__ < 10) begin \
      foreach(ARG[i]) begin \
        string nm__ = $sformatf("%s[%0d]", `"ARG`", i); \
        `uvm_record_string(nm__, ARG[i]) \
      end \
    end \
    else begin \
      for(int i=0; i<5; ++i) begin \
        string nm__ = $sformatf("%s[%0d]", `"ARG`", i); \
        `uvm_record_string(nm__, ARG[i]) \
      end \
      for(int i=sz__-5; i<sz__; ++i) begin \
        string nm__ = $sformatf("%s[%0d]", `"ARG`", i); \
        `uvm_record_string(nm__, ARG[i]) \
      end \
    end \
  end
		 
// uvm_record_qda_real
// ---------------------

`define uvm_record_qda_real(ARG) \
  begin \
    int sz__; \
    /* workaround for sarray real + $size */ \
    foreach (ARG[i]) \
      sz__ = i; \
    if(sz__ == 0) begin \
      `uvm_record_int(`"ARG`", 0, 32, UVM_DEC) \
    end \
    else if(sz__ < 10) begin \
      foreach(ARG[i]) begin \
        string nm__ = $sformatf("%s[%0d]", `"ARG`", i); \
        `uvm_record_real(nm__, ARG[i]) \
      end \
    end \
    else begin \
      for(int i=0; i<5; ++i) begin \
        string nm__ = $sformatf("%s[%0d]", `"ARG`", i); \
        `uvm_record_real(nm__, ARG[i]) \
      end \
      for(int i=sz__-5; i<sz__; ++i) begin \
        string nm__ = $sformatf("%s[%0d]", `"ARG`", i); \
        `uvm_record_real(nm__, ARG[i]) \
      end \
    end \
  end


`endif // UVM_RECORDER_DEFINES_SVH
