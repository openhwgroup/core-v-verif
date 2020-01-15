//----------------------------------------------------------------------
// Copyright 2007-2011 Mentor Graphics Corporation
// Copyright 2017-2018 Intel Corporation
// Copyright 2007-2018 Cadence Design Systems, Inc.
// Copyright 2013-2018 NVIDIA Corporation
// Copyright 2017-2018 Cisco Systems, Inc.
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
//
// MACROS for uvm_printer usage
//
// Provides a set of printing macros that will call appropriate print methods
// inside of a uvm_printer object. All macros have two versions: one assumes
// that the name of the value is the string-ized value, whereas the other takes
// an explicit name.
//
//------------------------------------------------------------------------------

`ifndef UVM_PRINTER_DEFINES_SVH
`define UVM_PRINTER_DEFINES_SVH

// uvm_print_int
// --------------

`define uvm_print_int(VALUE, SIZE, RADIX=UVM_NORADIX, VALUE_TYPE=integral, PRINTER=printer) \
  `uvm_print_named_int(`"VALUE`", VALUE, SIZE, RADIX, VALUE_TYPE, PRINTER)

`define uvm_print_named_int(NAME, VALUE, SIZE, RADIX=UVM_NORADIX, VALUE_TYPE=integral, PRINTER=printer) \
if (SIZE > 64) \
  PRINTER.print_field(NAME, VALUE, SIZE, RADIX, ".", `"VALUE_TYPE`"); \
else \
  PRINTER.print_field_int(NAME, VALUE, SIZE, RADIX, ".", `"VALUE_TYPE`");

// uvm_print_real
// --------------

`define uvm_print_real(VALUE, PRINTER=printer) \
  `uvm_print_named_real(`"VALUE`", VALUE, PRINTER)

`define uvm_print_named_real(NAME, VALUE, PRINTER=printer) \
  PRINTER.print_real(NAME, VALUE); 

// uvm_print_enum
// --------------

`define uvm_print_enum(TYPE, VALUE, PRINTER=printer) \
  `uvm_print_named_enum(TYPE, `"VALUE`", VALUE, PRINTER)

`define uvm_print_named_enum(TYPE, NAME, VALUE, PRINTER=printer) \
if (VALUE.name()  == "") \
  `uvm_print_named_int(NAME, VALUE, $bits(VALUE), UVM_NORADIX, TYPE, PRINTER) \
else \
  PRINTER.print_generic(NAME, `"TYPE`", $bits(VALUE), VALUE.name());

// uvm_print_object*
// -----------------

`define uvm_print_object(VALUE, RECURSION_POLICY=UVM_DEFAULT_POLICY, PRINTER=printer) \
  `uvm_print_named_object(`"VALUE`", VALUE, RECURSION_POLICY, PRINTER)

`define uvm_print_named_object(NAME, VALUE, RECURSION_POLICY=UVM_DEFAULT_POLICY, PRINTER=printer) \
if ((RECURSION_POLICY != UVM_DEFAULT_POLICY) && \
    (RECURSION_POLICY != PRINTER.get_recursion_policy())) begin \
  uvm_recursion_policy_enum __saved_recursion_policy  = PRINTER.get_recursion_policy(); \
  PRINTER.set_recursion_policy(RECURSION_POLICY); \
  `m_uvm_print_named_object(NAME, VALUE, PRINTER) \
  PRINTER.set_recursion_policy(__saved_recursion_policy); \
end \
else begin \
  `m_uvm_print_named_object(NAME, VALUE, PRINTER) \
end

    
`define m_uvm_print_named_object(NAME, VALUE, PRINTER) \
if (PRINTER.object_printed(VALUE, PRINTER.get_recursion_policy()) != uvm_policy::NEVER) begin \
  uvm_recursion_policy_enum __saved_recursion_policy = PRINTER.get_recursion_policy(); \
  PRINTER.set_recursion_policy(UVM_REFERENCE); \
  PRINTER.print_object(NAME, VALUE); \
  PRINTER.set_recursion_policy(__saved_recursion_policy); \
end \
else begin \
  PRINTER.print_object(NAME, VALUE); \
end    

// uvm_print_string*
// -----------------

`define uvm_print_string(VALUE, PRINTER=printer) \
  `uvm_print_named_string(`"VALUE`", VALUE, PRINTER)

`define uvm_print_named_string(NAME, VALUE, PRINTER=printer) \
  PRINTER.print_string(NAME, VALUE);

////////////////////////
// Array Printing Below
////////////////////////

// Arrays of ints

`define uvm_print_qda_int(ARRAY_TYPE, VALUE, RADIX=UVM_NORADIX, VALUE_TYPE=integral, PRINTER=printer) \
  `uvm_print_named_qda_int(ARRAY_TYPE, `"VALUE`", VALUE, RADIX, VALUE_TYPE, PRINTER)
    
`define uvm_print_named_qda_int(ARRAY_TYPE, NAME, VALUE, RADIX=UVM_NORADIX, VALUE_TYPE=integral, PRINTER=printer) \
begin \
  int __tmp_max = $right(VALUE) + 1; \
  PRINTER.print_array_header(NAME, \
                             __tmp_max, \
                             `"ARRAY_TYPE``(``VALUE_TYPE``)`"); \
  if ((PRINTER.get_max_depth() == -1) || \
      (PRINTER.get_active_object_depth() < PRINTER.get_max_depth()+1)) begin \
    int __tmp_begin_elements, __tmp_end_elements; \
    __tmp_begin_elements      = PRINTER.get_begin_elements(); \
    __tmp_end_elements        = PRINTER.get_end_elements(); \
    /* Fast Bypass */ \
    if (__tmp_begin_elements == -1 || __tmp_end_elements == -1) begin \
      foreach (VALUE[__tmp_index]) begin \
        `uvm_print_named_int($sformatf("[%0d]", __tmp_index), \
                             VALUE[__tmp_index], \
                             $bits(VALUE[__tmp_index]), \
                             RADIX, \
                             VALUE_TYPE, \
                             PRINTER) \
      end \
    end \
    else begin \
      int __tmp_curr; \
      foreach(VALUE[__tmp_index]) begin \
        if (__tmp_curr < __tmp_begin_elements) begin \
          `uvm_print_named_int($sformatf("[%0d]", __tmp_index), \
                               VALUE[__tmp_index], \
                               $bits(VALUE[__tmp_index]), \
                               RADIX, \
                               VALUE_TYPE, \
                               PRINTER) \
        end \
        else \
          break; \
        __tmp_curr++; \
      end \
      if (__tmp_curr < __tmp_max ) begin \
        if ((__tmp_max - __tmp_end_elements) > __tmp_curr) \
          __tmp_curr  = __tmp_max - __tmp_end_elements; \
        if (__tmp_curr < __tmp_begin_elements) \
          __tmp_curr = __tmp_begin_elements; \
        else \
          PRINTER.print_array_range(__tmp_begin_elements, __tmp_curr-1); \
        while (__tmp_curr < __tmp_max) begin \
          `uvm_print_named_int($sformatf("[%0d]", __tmp_curr), \
                               VALUE[__tmp_curr], \
                               $bits(VALUE[__tmp_curr]), \
                               RADIX, \
                               VALUE_TYPE, \
                               PRINTER) \
          __tmp_curr++; \
        end \
      end \
    end \
  end \
  PRINTER.print_array_footer(__tmp_max); \
end     
    
`define uvm_print_array_int(VALUE, RADIX=UVM_NORADIX, VALUE_TYPE=integral, PRINTER=printer) \
  `uvm_print_named_qda_int(da, `"VALUE`", VALUE, RADIX, VALUE_TYPE, PRINTER) 

`define uvm_print_named_array_int(NAME, VALUE, RADIX=UVM_NORADIX, VALUE_TYPE=integral, PRINTER=printer) \
  `uvm_print_named_qda_int(da, NAME, VALUE, RADIX, VALUE_TYPE, PRINTER)

`define uvm_print_sarray_int(VALUE, RADIX=UVM_RADIX, VALUE_TYPE=integral, PRINTER=printer) \
  `uvm_print_named_qda_int(sa, `"VALUE`", VALUE, RADIX, VALUE_TYPE, PRINTER)

`define uvm_print_named_sarray_int(NAME, VALUE, RADIX=UVM_NORADIX, VALUE_TYPE=integral, PRINTER=printer) \
  `uvm_print_named_qda_int(sa, NAME, VALUE, RADIX, VALUE_TYPE, PRINTER)

`define uvm_print_queue_int(VALUE, RADIX=UVM_NORADIX, VALUE_TYPE=integral, PRINTER=printer) \
  `uvm_print_named_qda_int(queue, `"VALUE`", VALUE, RADIX, VALUE_TYPE, PRINTER)

`define uvm_print_named_queue_int(NAME, VALUE, RADIX=UVM_NORADIX, VALUE_TYPE=integral, PRINTER=printer) \
  `uvm_print_named_qda_int(queue, NAME, VALUE, RADIX, VALUE_TYPE, PRINTER)
    
// Arrays of reals

`define uvm_print_qda_real(ARRAY_TYPE, VALUE, PRINTER=printer) \
  `uvm_print_named_qda_real(ARRAY_TYPE, `"VALUE`", VALUE, PRINTER) 
    
`define uvm_print_named_qda_real(ARRAY_TYPE, NAME, VALUE, PRINTER=printer) \
begin \
  int __tmp_max = $right(VALUE) + 1; \
  PRINTER.print_array_header(NAME, \
                             __tmp_max, \
                             `"ARRAY_TYPE``(real)`"); \
  if ((PRINTER.get_max_depth() == -1) || \
      (PRINTER.get_active_object_depth() < PRINTER.get_max_depth()+1)) begin \
    int __tmp_begin_elements, __tmp_end_elements; \
    __tmp_begin_elements    = PRINTER.get_begin_elements(); \
    __tmp_end_elements      = PRINTER.get_end_elements(); \
    /* Fast Bypass */ \
    if (__tmp_begin_elements == -1 || __tmp_end_elements == -1) begin \
      foreach (VALUE[__tmp_index]) begin \
        `uvm_print_named_real($sformatf("[%0d]", __tmp_index), \
                                VALUE[__tmp_index], \
                                PRINTER) \
      end \
    end \
    else begin \
      int __tmp_curr; \
      foreach(VALUE[__tmp_index]) begin \
        if (__tmp_curr < __tmp_begin_elements) begin \
          `uvm_print_named_real($sformatf("[%0d]", __tmp_index), \
                                  VALUE[__tmp_index], \
                                  PRINTER) \
        end \
        else \
          break; \
        __tmp_curr++; \
      end \
      if (__tmp_curr < __tmp_max ) begin \
        if ((__tmp_max - __tmp_end_elements) > __tmp_curr) \
          __tmp_curr  = __tmp_max - __tmp_end_elements; \
        if (__tmp_curr < __tmp_begin_elements) \
          __tmp_curr = __tmp_begin_elements; \
        else \
          PRINTER.print_array_range(__tmp_begin_elements, __tmp_curr-1); \
        while (__tmp_curr < __tmp_max) begin \
          `uvm_print_named_real($sformatf("[%0d]", __tmp_curr), \
                                  VALUE[__tmp_curr], \
                                  PRINTER) \
          __tmp_curr++; \
        end \
      end \
    end \
  end \
  PRINTER.print_array_footer(__tmp_max); \
end     
    
`define uvm_print_array_real(VALUE, PRINTER=printer) \
  `uvm_print_named_qda_real(da, `"VALUE`", VALUE, PRINTER) 

`define uvm_print_named_array_real(NAME, VALUE, PRINTER=printer) \
  `uvm_print_named_qda_real(da, NAME, VALUE, PRINTER)

`define uvm_print_sarray_real(VALUE, PRINTER=printer) \
  `uvm_print_named_qda_real(sa, `"VALUE`", VALUE, PRINTER)

`define uvm_print_named_sarray_real(NAME, VALUE, PRINTER=printer) \
  `uvm_print_named_qda_real(sa, NAME, VALUE, PRINTER)

`define uvm_print_queue_real(VALUE,PRINTER=printer) \
  `uvm_print_named_qda_real(queue, `"VALUE`", VALUE, PRINTER)

`define uvm_print_named_queue_real(NAME, VALUE, PRINTER=printer) \
  `uvm_print_named_qda_real(queue, NAME, VALUE, PRINTER)

// Arrays of enums

`define uvm_print_qda_enum(ARRAY_TYPE, TYPE, VALUE, PRINTER=printer) \
  `uvm_print_named_qda_enum(ARRAY_TYPE, TYPE, `"VALUE`", VALUE, PRINTER)
    
`define uvm_print_named_qda_enum(ARRAY_TYPE, TYPE, NAME, VALUE, PRINTER=printer) \
begin \
  int __tmp_max = $right(VALUE) + 1; \
  PRINTER.print_array_header(NAME, \
                             __tmp_max, \
                             {`"ARRAY_TYPE``(`", `"TYPE`", ")"}); \
  if ((PRINTER.get_max_depth() == -1) || \
      (PRINTER.get_active_object_depth() < PRINTER.get_max_depth()+1)) begin \
    int __tmp_begin_elements, __tmp_end_elements; \
    __tmp_begin_elements      = PRINTER.get_begin_elements(); \
    __tmp_end_elements        = PRINTER.get_end_elements(); \
    /* Fast Bypass */ \
    if (__tmp_begin_elements == -1 || __tmp_end_elements == -1) begin \
      foreach (VALUE[__tmp_index]) begin \
        `uvm_print_named_enum(TYPE, \
                              $sformatf("[%0d]", __tmp_index), \
                              VALUE[__tmp_index], \
                              PRINTER) \
      end \
    end \
    else begin \
      int __tmp_curr; \
      foreach(VALUE[__tmp_index]) begin \
        if (__tmp_curr < __tmp_begin_elements) begin \
          `uvm_print_named_enum(TYPE, \
                                $sformatf("[%0d]", __tmp_index), \
                                VALUE[__tmp_index], \
                                PRINTER) \
        end \
        else \
          break; \
        __tmp_curr++; \
      end \
      if (__tmp_curr < __tmp_max ) begin \
        if ((__tmp_max - __tmp_end_elements) > __tmp_curr) \
          __tmp_curr  = __tmp_max - __tmp_end_elements; \
        if (__tmp_curr < __tmp_begin_elements) \
          __tmp_curr = __tmp_begin_elements; \
        else \
          PRINTER.print_array_range(__tmp_begin_elements, __tmp_curr-1); \
        while (__tmp_curr < __tmp_max) begin \
          `uvm_print_named_enum(TYPE, \
                                $sformatf("[%0d]", __tmp_curr), \
                                VALUE[__tmp_curr], \
                                PRINTER) \
          __tmp_curr++; \
        end \
      end \
    end \
  end \
  PRINTER.print_array_footer(__tmp_max); \
end     
    
`define uvm_print_array_enum(TYPE, VALUE, PRINTER=printer) \
  `uvm_print_named_qda_enum(da, `"VALUE`", TYPE, VALUE, PRINTER) 

`define uvm_print_named_array_enum(TYPE, NAME, VALUE, PRINTER=printer) \
  `uvm_print_named_qda_enum(da, TYPE, NAME, VALUE, PRINTER)

`define uvm_print_sarray_enum(TYPE, VALUE, PRINTER=printer) \
  `uvm_print_named_qda_enum(sa, TYPE, `"VALUE`", VALUE, PRINTER)

`define uvm_print_named_sarray_enum(TYPE, NAME, VALUE, PRINTER=printer) \
  `uvm_print_named_qda_enum(sa, TYPE, NAME, VALUE, PRINTER)

`define uvm_print_queue_enum(TYPE, VALUE, PRINTER=printer) \
  `uvm_print_named_qda_enum(queue, TYPE, `"VALUE`", VALUE, PRINTER)

`define uvm_print_named_queue_enum(TYPE, NAME, VALUE, PRINTER=printer) \
  `uvm_print_named_qda_enum(queue, TYPE, NAME, VALUE, PRINTER)
    
// Arrays of objects

`define uvm_print_qda_object(ARRAY_TYPE, VALUE, RECURSION_POLICY=UVM_DEFAULT_POLICY, PRINTER=printer) \
  `uvm_print_named_qda_object(ARRAY_TYPE, `"VALUE`", VALUE, RECURSION_POLICY, PRINTER)    
    
`define uvm_print_named_qda_object(ARRAY_TYPE, NAME, VALUE, RECURSION_POLICY=UVM_DEFAULT_POLICY, PRINTER=printer) \
begin \
  int __tmp_max = $right(VALUE) + 1; \
  PRINTER.print_array_header(NAME, \
                             __tmp_max, \
                             `"ARRAY_TYPE``(object)`"); \
  if ((PRINTER.get_max_depth() == -1) || \
      (PRINTER.get_active_object_depth() < PRINTER.get_max_depth()+1)) begin \
    uvm_recursion_policy_enum __tmp_recursion_policy; \
    int __tmp_begin_elements, __tmp_end_elements; \
    __tmp_begin_elements    = PRINTER.get_begin_elements(); \
    __tmp_end_elements      = PRINTER.get_end_elements(); \
    __tmp_recursion_policy  = PRINTER.get_recursion_policy(); \
    if ((RECURSION_POLICY != UVM_DEFAULT_POLICY) && \
        (__tmp_recursion_policy != RECURSION_POLICY)) \
      PRINTER.set_recursion_policy(RECURSION_POLICY); \
    /* Fast Bypass */ \
    if (__tmp_begin_elements == -1 || __tmp_end_elements == -1) begin \
      foreach (VALUE[__tmp_index]) begin \
        `m_uvm_print_named_object($sformatf("[%0d]", __tmp_index), \
                                  VALUE[__tmp_index], \
                                  PRINTER) \
      end \
    end \
    else begin \
      int __tmp_curr; \
      foreach(VALUE[__tmp_index]) begin \
        if (__tmp_curr < __tmp_begin_elements) begin \
          `m_uvm_print_named_object($sformatf("[%0d]", __tmp_index), \
                                    VALUE[__tmp_index], \
                                    PRINTER) \
        end \
        else \
          break; \
        __tmp_curr++; \
      end \
      if (__tmp_curr < __tmp_max ) begin \
        if ((__tmp_max - __tmp_end_elements) > __tmp_curr) \
          __tmp_curr  = __tmp_max - __tmp_end_elements; \
        if (__tmp_curr < __tmp_begin_elements) \
          __tmp_curr = __tmp_begin_elements; \
        else \
          PRINTER.print_array_range(__tmp_begin_elements, __tmp_curr-1); \
        while (__tmp_curr < __tmp_max) begin \
          `m_uvm_print_named_object($sformatf("[%0d]", __tmp_curr), \
                                    VALUE[__tmp_curr], \
                                    PRINTER) \
          __tmp_curr++; \
        end \
      end \
    end \
    if ((RECURSION_POLICY != UVM_DEFAULT_POLICY) && \
        (__tmp_recursion_policy != RECURSION_POLICY)) \
      PRINTER.set_recursion_policy(__tmp_recursion_policy); \
  end \
  PRINTER.print_array_footer(__tmp_max); \
end     
    
`define uvm_print_array_object(VALUE, RECURSION_POLICY=UVM_DEFAULT_POLICY, PRINTER=printer) \
  `uvm_print_named_qda_object(da, `"VALUE`", VALUE, RECURSION_POLICY, PRINTER) 

`define uvm_print_named_array_object(NAME, VALUE, RECURSION_POLICY=UVM_DEFAULT_POLICY, PRINTER=printer) \
  `uvm_print_named_qda_object(da, NAME, VALUE, RECURSION_POLICY, PRINTER)

`define uvm_print_sarray_object(VALUE, RECURSION_POLICY=UVM_DEFAULT_POLICY, PRINTER=printer) \
  `uvm_print_named_qda_object(sa, `"VALUE`", VALUE, RECURSION_POLICY, PRINTER)

`define uvm_print_named_sarray_object(NAME, VALUE, RECURSION_POLICY=UVM_DEFAULT_POLICY, PRINTER=printer) \
  `uvm_print_named_qda_object(sa, NAME, VALUE, RECURSION_POLICY, PRINTER)

`define uvm_print_queue_object(VALUE, RECURSION_POLICY=UVM_DEFAULT_POLICY, PRINTER=printer) \
  `uvm_print_named_qda_object(queue, `"VALUE`", VALUE, RECURSION_POLICY, PRINTER)

`define uvm_print_named_queue_object(NAME, VALUE, RECURSION_POLICY=UVM_DEFAULT_POLICY, PRINTER=printer) \
  `uvm_print_named_qda_object(queue, NAME, VALUE, RECURSION_POLICY, PRINTER)

// Arrays of strings

`define uvm_print_qda_string(ARRAY_TYPE, VALUE, PRINTER=printer) \
  `uvm_print_named_qda_string(ARRAY_TYPE, `"VALUE`", VALUE, PRINTER)
    
`define uvm_print_named_qda_string(ARRAY_TYPE, NAME, VALUE, PRINTER=printer) \
begin \
  int __tmp_max = $right(VALUE) + 1; \
  PRINTER.print_array_header(NAME, \
                             __tmp_max, \
                             `"ARRAY_TYPE``(string)`"); \
  if ((PRINTER.get_max_depth() == -1) || \
      (PRINTER.get_active_object_depth() < PRINTER.get_max_depth()+1)) begin \
    int __tmp_begin_elements, __tmp_end_elements; \
    __tmp_begin_elements    = PRINTER.get_begin_elements(); \
    __tmp_end_elements      = PRINTER.get_end_elements(); \
    /* Fast Bypass */ \
    if (__tmp_begin_elements == -1 || __tmp_end_elements == -1) begin \
      foreach (VALUE[__tmp_index]) begin \
        `uvm_print_named_string($sformatf("[%0d]", __tmp_index), \
                                VALUE[__tmp_index], \
                                PRINTER) \
      end \
    end \
    else begin \
      int __tmp_curr; \
      foreach(VALUE[__tmp_index]) begin \
        if (__tmp_curr < __tmp_begin_elements) begin \
          `uvm_print_named_string($sformatf("[%0d]", __tmp_index), \
                                  VALUE[__tmp_index], \
                                  PRINTER) \
        end \
        else \
          break; \
        __tmp_curr++; \
      end \
      if (__tmp_curr < __tmp_max ) begin \
        if ((__tmp_max - __tmp_end_elements) > __tmp_curr) \
          __tmp_curr  = __tmp_max - __tmp_end_elements; \
        if (__tmp_curr < __tmp_begin_elements) \
          __tmp_curr = __tmp_begin_elements; \
        else \
          PRINTER.print_array_range(__tmp_begin_elements, __tmp_curr-1); \
        while (__tmp_curr < __tmp_max) begin \
          `uvm_print_named_string($sformatf("[%0d]", __tmp_curr), \
                                  VALUE[__tmp_curr], \
                                  PRINTER) \
          __tmp_curr++; \
        end \
      end \
    end \
  end \
  PRINTER.print_array_footer(__tmp_max); \
end     
    
`define uvm_print_array_string(VALUE, PRINTER=printer) \
  `uvm_print_named_qda_string(da, `"VALUE`", VALUE, PRINTER) 

`define uvm_print_named_array_string(NAME, VALUE, PRINTER=printer) \
  `uvm_print_named_qda_string(da, NAME, VALUE, PRINTER)

`define uvm_print_sarray_string(VALUE, PRINTER=printer) \
  `uvm_print_named_qda_string(sa, `"VALUE`", VALUE, PRINTER)

`define uvm_print_named_sarray_string(NAME, VALUE, PRINTER=printer) \
  `uvm_print_named_qda_string(sa, NAME, VALUE, PRINTER)

`define uvm_print_queue_string(VALUE, PRINTER=printer) \
  `uvm_print_named_qda_string(queue, `"VALUE`", VALUE, PRINTER)

`define uvm_print_named_queue_string(NAME, VALUE, PRINTER=printer) \
  `uvm_print_named_qda_string(queue, NAME, VALUE, PRINTER)

//-----------------------------------------------------------------------------
//
// Associative array printing methods
//
//-----------------------------------------------------------------------------

`define uvm_print_aa_int_string(VALUE, RADIX=UVM_NORADIX, VALUE_TYPE=integral, PRINTER=printer) \
  `uvm_print_named_aa_int_string(`"VALUE`", VALUE, RADIX, VALUE_TYPE, PRINTER)

`define uvm_print_named_aa_int_string(NAME, VALUE, RADIX=UVM_NORADIX, VALUE_TYPE=integral, PRINTER=printer) \
begin \
  PRINTER.print_array_header(NAME, \
                             VALUE.num(), \
                             `"aa(``VALUE_TYPE``,string)`"); \
  if ((PRINTER.get_max_depth() == -1) || \
      (PRINTER.get_active_object_depth() < PRINTER.get_max_depth()+1)) begin \
    foreach(VALUE[__tmp_index]) \
      `uvm_print_named_int($sformatf("[%s]", __tmp_index), \
                           VALUE[__tmp_index], \
                           $bits(VALUE[__tmp_index]), \
                           RADIX, \
                           VALUE_TYPE, \
                           PRINTER ) \
  end \
  PRINTER.print_array_footer(VALUE.num()); \
end

`define uvm_print_aa_object_string(VALUE, RECURSION_POLICY=UVM_DEFAULT_POLICY, PRINTER=printer) \
  `uvm_print_named_aa_object_string(`"VALUE`", VALUE, RECURSION_POLICY, PRINTER)

`define uvm_print_named_aa_object_string(NAME, VALUE, RECURSION_POLICY=UVM_DEFAULT_POLICY, PRINTER=printer) \
begin \
  PRINTER.print_array_header(NAME, \
                             VALUE.num(), \
                             "aa(object,string)"); \
  if ((PRINTER.get_max_depth() == -1) || \
      (PRINTER.get_active_object_depth() < PRINTER.get_max_depth()+1)) begin \
    uvm_recursion_policy_enum __tmp_recursion_policy; \
    __tmp_recursion_policy  = PRINTER.get_recursion_policy(); \
    if ((RECURSION_POLICY != UVM_DEFAULT_POLICY) && \
        (__tmp_recursion_policy != RECURSION_POLICY)) \
      PRINTER.set_recursion_policy(RECURSION_POLICY); \
    foreach(VALUE[__tmp_index]) \
      `m_uvm_print_named_object($sformatf("[%s]", __tmp_index), \
                                VALUE[__tmp_index], \
                                PRINTER ) \
    if ((RECURSION_POLICY != UVM_DEFAULT_POLICY) && \
        (__tmp_recursion_policy != RECURSION_POLICY)) \
      PRINTER.set_recursion_policy(__tmp_recursion_policy); \
  end \
  PRINTER.print_array_footer(VALUE.num()); \
end

`define uvm_print_aa_string_string(VALUE, PRINTER=printer) \
  `uvm_print_named_aa_string_string(`"VALUE`", VALUE, PRINTER)

`define uvm_print_named_aa_string_string(NAME, VALUE, PRINTER=printer) \
begin \
  PRINTER.print_array_header(NAME, \
                             VALUE.num(), \
                             "aa(string,string)"); \
  if ((PRINTER.get_max_depth() == -1) || \
      (PRINTER.get_active_object_depth() < PRINTER.get_max_depth()+1)) begin \
    foreach(VALUE[__tmp_index]) \
      `uvm_print_named_string($sformatf("[%s]", __tmp_index), \
                              VALUE[__tmp_index], \
                              PRINTER ) \
  end \
  PRINTER.print_array_footer(VALUE.num()); \
end

`define uvm_print_aa_int_int(VALUE, RADIX=UVM_NORADIX, VALUE_TYPE=int, INDEX_TYPE=int, PRINTER=printer) \
  `uvm_print_named_aa_int_int(`"VALUE`", VALUE, RADIX, VALUE_TYPE, INDEX_TYPE, PRINTER)

`define uvm_print_named_aa_int_int(NAME, VALUE, RADIX=UVM_NORADIX, VALUE_TYPE=int, INDEX_TYPE=int, PRINTER=printer) \
begin \
  PRINTER.print_array_header(NAME, \
                             VALUE.num(), \
                             `"aa(``VALUE_TYPE``,``INDEX_TYPE``)`"); \
  if ((PRINTER.get_max_depth() == -1) || \
      (PRINTER.get_active_object_depth() < PRINTER.get_max_depth()+1)) begin \
    foreach(VALUE[__tmp_index]) \
      `uvm_print_named_int($sformatf("[%0d]", __tmp_index), \
                           VALUE[__tmp_index], \
                           $bits(VALUE[__tmp_index]), \
                           RADIX, \
                           VALUE_TYPE, \
                           PRINTER ) \
  end \
  PRINTER.print_array_footer(VALUE.num()); \
end

`define uvm_print_aa_object_int(VALUE, RECURSION_POLICY=UVM_DEFAULT_POLICY, INDEX_TYPE=int, PRINTER=printer) \
  `uvm_print_named_aa_object_int(`"VALUE`", VALUE, RECURSION_POLICY, INDEX_TYPE, PRINTER)

`define uvm_print_named_aa_object_int(NAME, VALUE, RECURSION_POLICY=UVM_DEFAULT_POLICY, INDEX_TYPE=int, PRINTER=printer) \
begin \
  PRINTER.print_array_header(NAME, \
                             VALUE.num(), \
                             `"aa(object,``INDEX_TYPE``)`"); \
  if ((PRINTER.get_max_depth() == -1) || \
      (PRINTER.get_active_object_depth() < PRINTER.get_max_depth()+1)) begin \
    uvm_recursion_policy_enum __tmp_recursion_policy; \
    __tmp_recursion_policy  = PRINTER.get_recursion_policy(); \
    if ((RECURSION_POLICY != UVM_DEFAULT_POLICY) && \
        (__tmp_recursion_policy != RECURSION_POLICY)) \
      PRINTER.set_recursion_policy(RECURSION_POLICY); \
    foreach(VALUE[__tmp_index]) \
      `m_uvm_print_named_object($sformatf("[%0d]", __tmp_index), \
                                VALUE[__tmp_index], \
                                PRINTER ) \
    if ((RECURSION_POLICY != UVM_DEFAULT_POLICY) && \
        (__tmp_recursion_policy != RECURSION_POLICY)) \
      PRINTER.set_recursion_policy(__tmp_recursion_policy); \
  end \
  PRINTER.print_array_footer(VALUE.num()); \
end

`define uvm_print_aa_string_int(VALUE, INDEX_TYPE=int, PRINTER=printer) \
  `uvm_print_named_aa_string_int(`"VALUE`", VALUE, INDEX_TYPE, PRINTER)

`define uvm_print_named_aa_string_int(NAME, VALUE, INDEX_TYPE=int, PRINTER=printer) \
begin \
  PRINTER.print_array_header(NAME, \
                             VALUE.num(), \
                             `"aa(string,``INDEX_TYPE``)`"); \
  if ((PRINTER.get_max_depth() == -1) || \
      (PRINTER.get_active_object_depth() < PRINTER.get_max_depth()+1)) begin \
    foreach(VALUE[__tmp_index]) \
      `uvm_print_named_string($sformatf("[%0d]", __tmp_index), \
                              VALUE[__tmp_index], \
                              PRINTER ) \
  end \
  PRINTER.print_array_footer(VALUE.num()); \
end

`define uvm_print_aa_int_enum(ENUM_TYPE, VALUE, RADIX=UVM_NORADIX, VALUE_TYPE=int, PRINTER=printer) \
  `uvm_print_named_aa_int_enum(`"VALUE`", ENUM_TYPE, VALUE, RADIX, VALUE_TYPE, PRINTER)

`define uvm_print_named_aa_int_enum(NAME, ENUM_TYPE, VALUE, RADIX=UVM_NORADIX, VALUE_TYPE=int, PRINTER=printer) \
begin \
  PRINTER.print_array_header(NAME, \
                             VALUE.num(), \
                             `"aa(``VALUE_TYPE``,``ENUM_TYPE``)`"); \
  if ((PRINTER.get_max_depth() == -1) || \
      (PRINTER.get_active_object_depth() < PRINTER.get_max_depth()+1)) begin \
    foreach(VALUE[__tmp_index]) \
      `uvm_print_named_int((__tmp_index.name() == "") ? $sformatf("[%s'(%0d)]", `"ENUM_TYPE`",__tmp_index) \
                                                      : $sformatf("[%s]", __tmp_index.name()), \
                           VALUE[__tmp_index], \
                           $bits(VALUE[__tmp_index]), \
                           RADIX, \
                           VALUE_TYPE, \
                           PRINTER ) \
  end \
  PRINTER.print_array_footer(VALUE.num()); \
end

    
`endif //  `ifndef UVM_PRINTER_DEFINES_SVH

