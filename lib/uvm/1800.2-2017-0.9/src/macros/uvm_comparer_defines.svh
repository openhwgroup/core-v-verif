//----------------------------------------------------------------------
// Copyright 2018 Cadence Design Systems, Inc.
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
//
// MACROS for uvm_comparer usage
//
// Provides a set of comparison macros that will call appropriate methods
// inside of a uvm_comparer object.
//
//------------------------------------------------------------------------------

`ifndef UVM_COMPARER_DEFINES_SVH
 `define UVM_COMPARER_DEFINES_SVH

// m_uvm_compare_threshold_begin/end
`define m_uvm_compare_threshold_begin(COMPARER) \
  if ((!COMPARER.get_threshold() || \
       (COMPARER.get_result() < COMPARER.get_threshold()))) begin \

`define m_uvm_compare_threshold_end \
  end

// m_uvm_compare_begin/end
`define m_uvm_compare_begin(LVALUE, RVALUE, COMPARER=comparer) \
  `m_uvm_compare_threshold_begin(COMPARER) \
    if ((LVALUE) !== (RVALUE)) begin \

`define m_uvm_compare_end \
    end \
  `m_uvm_compare_threshold_end

// uvm_compare_int
`define uvm_compare_int(LVALUE, RVALUE, RADIX, COMPARER=comparer) \
  `uvm_compare_named_int(`"LVALUE`", LVALUE, RVALUE, RADIX, COMPARER)

`define uvm_compare_named_int(NAME, LVALUE, RVALUE, RADIX, COMPARER=comparer) \
  `m_uvm_compare_begin(LVALUE, RVALUE, COMPARER) \
     if ($bits(LVALUE) <= 64) \
       void'(COMPARER.compare_field_int(NAME , LVALUE, RVALUE, $bits(LVALUE), RADIX)); \
     else \
       void'(COMPARER.compare_field(NAME , LVALUE, RVALUE, $bits(LVALUE), RADIX)); \
  `m_uvm_compare_end 

// uvm_compare_enum

`define uvm_compare_enum(LVALUE, RVALUE, TYPE, COMPARER=comparer) \
  `uvm_compare_named_enum(`"LVALUE`", LVALUE, RVALUE, TYPE, COMPARER) 

`define uvm_compare_named_enum(NAME, LVALUE, RVALUE, TYPE, COMPARER=comparer) \
  `m_uvm_compare_begin(LVALUE, RVALUE, COMPARER) \
     void'(COMPARER.compare_string(NAME , \
                                   $sformatf("%s'(%s)", `"TYPE`", LVALUE.name()), \
                                   $sformatf("%s'(%s)", `"TYPE`", RVALUE.name())) ); \
  `m_uvm_compare_end 

// uvm_compare_real

`define uvm_compare_real(LVALUE, RVALUE, COMPARER=comparer) \
  `uvm_compare_named_real(`"LVALUE`", LVALUE, RVALUE, COMPARER) 
                                                        
`define uvm_compare_named_real(NAME, LVALUE, RVALUE, COMPARER=comparer) \
  `m_uvm_compare_threshold_begin(COMPARER) \
    if ((LVALUE) != (RVALUE)) begin \
      void'(COMPARER.compare_field_real(NAME , LVALUE, RVALUE)); \
    end \
  `m_uvm_compare_threshold_end 

// uvm_compare_object

`define uvm_compare_object(LVALUE, RVALUE, POLICY=UVM_DEFAULT_POLICY, COMPARER=comparer) \
  `uvm_compare_named_object(`"LVALUE`", LVALUE, RVALUE, POLICY, COMPARER)
    
`define uvm_compare_named_object(NAME, LVALUE, RVALUE, POLICY=UVM_DEFAULT_POLICY, COMPARER=comparer) \
  `m_uvm_compare_begin(LVALUE, RVALUE, COMPARER) \
     uvm_recursion_policy_enum prev_rec__; \
     prev_rec__ = COMPARER.get_recursion_policy(); \
     if (POLICY != UVM_DEFAULT_POLICY) \
       COMPARER.set_recursion_policy(POLICY); \
     `m_uvm_compare_named_object(NAME, LVALUE, RVALUE, COMPARER) \
     if (POLICY != UVM_DEFAULT_POLICY) \
       COMPARER.set_recursion_policy(prev_rec__); \
  `m_uvm_compare_end

// This macro skips the recursion policy check, which allows it to be efficiently
// reused by other object macros.
`define m_uvm_compare_named_object(NAME, LVALUE, RVALUE, COMPARER) \
  if (COMPARER.get_recursion_policy() != UVM_REFERENCE) begin \
    bit rv; \
    uvm_policy::recursion_state_e state; \
    state = COMPARER.object_compared(LVALUE, RVALUE, COMPARER.get_recursion_policy(), rv); \
    if ((state == uvm_policy::FINISHED) && \
        !rv) \
      COMPARER.print_msg($sformatf("'%s' miscompared using saved return value", NAME)); \
    else if (state == uvm_policy::NEVER) \
      void'(COMPARER.compare_object(NAME, LVALUE, RVALUE)); \
    /* else skip to avoid infinite loop */ \
  end \
  else begin \
    void'(COMPARER.compare_object(NAME, LVALUE, RVALUE)); \
  end
                   

// uvm_compare_string

`define uvm_compare_string(LVALUE, RVALUE, COMPARER=comparer) \
  `uvm_compare_named_string(`"LVALUE`", LVALUE, RVALUE, COMPARER)
    
`define uvm_compare_named_string(NAME, LVALUE, RVALUE, COMPARER=comparer) \
  `m_uvm_compare_threshold_begin(COMPARER) \
    if ((LVALUE) != (RVALUE)) begin \
      void'(COMPARER.compare_string(NAME , LVALUE, RVALUE)); \
    end \
  `m_uvm_compare_threshold_end 


// uvm_compare_sarray_int

`define uvm_compare_sarray_int(LVALUE, RVALUE, RADIX, COMPARER=comparer) \
  `uvm_compare_named_sarray_int(`"LVALUE`", LVALUE, RVALUE, RADIX, COMPARER)
           
`define uvm_compare_named_sarray_int(NAME, LVALUE, RVALUE, RADIX, COMPARER=comparer) \
  `m_uvm_compare_begin(LVALUE, RVALUE, COMPARER) \
    foreach (LVALUE[i]) begin \
      `uvm_compare_named_int($sformatf("%s[%0d]", NAME, i), \
                             LVALUE[i], \
                             RVALUE[i], \
                             RADIX, \
                             COMPARER) \
    end \
  `m_uvm_compare_end

// uvm_compare_qda_int

`define uvm_compare_qda_int(LVALUE, RVALUE, RADIX, COMPARER=comparer) \
  `uvm_compare_named_qda_int(`"LVALUE`", LVALUE, RVALUE, RADIX, COMPARER)
    
`define uvm_compare_named_qda_int(NAME, LVALUE, RVALUE, RADIX, COMPARER=comparer) \
  `m_uvm_compare_begin(LVALUE, RVALUE, COMPARER) \
    `uvm_compare_named_int($sformatf("%s.size()", NAME), \
                           LVALUE.size(), \
                           RVALUE.size(), \
                           UVM_DEC, \
                           COMPARER) \
    `uvm_compare_named_sarray_int(NAME, LVALUE, RVALUE, RADIX, COMPARER) \
  `m_uvm_compare_end

// uvm_compare_sarray_real

`define uvm_compare_sarray_real(LVALUE, RVALUE, COMPARER=comparer) \
  `uvm_compare_named_sarray_real(`"LVALUE`", LVALUE, RVALUE,COMPARER)
           
`define uvm_compare_named_sarray_real(NAME, LVALUE, RVALUE, COMPARER=comparer) \
  `m_uvm_compare_threshold_begin(COMPARER) \
    if ((LVALUE) != (RVALUE)) begin \
      foreach (LVALUE[i]) begin \
        `uvm_compare_named_real($sformatf("%s[%0d]", NAME, i), \
                               LVALUE[i], \
                               RVALUE[i], \
                               COMPARER) \
      end \
    end \
  `m_uvm_compare_threshold_end

// uvm_compare_qda_real

`define uvm_compare_qda_real(LVALUE, RVALUE, COMPARER=comparer) \
  `uvm_compare_named_qda_real(`"LVALUE`", LVALUE, RVALUE, COMPARER)
    
`define uvm_compare_named_qda_real(NAME, LVALUE, RVALUE, COMPARER=comparer) \
  `m_uvm_compare_threshold_begin(COMPARER) \
    `uvm_compare_named_real($sformatf("%s.size()", NAME), \
                           LVALUE.size(), \
                           RVALUE.size(), \
                           COMPARER) \
    `uvm_compare_named_sarray_real(NAME, LVALUE, RVALUE, COMPARER) \
  `m_uvm_compare_threshold_end
           
           
// uvm_compare_sarray_enum

`define uvm_compare_sarray_enum(LVALUE, RVALUE, TYPE, COMPARER=comparer) \
  `uvm_compare_named_sarray_enum(`"LVALUE`", LVALUE, RVALUE, TYPE, COMPARER)
                                                            
`define uvm_compare_named_sarray_enum(NAME, LVALUE, RVALUE, TYPE, COMPARER=comparer) \
  `m_uvm_compare_begin(LVALUE, RVALUE, COMPARER) \
    foreach (LVALUE[i]) begin \
      `uvm_compare_named_enum($sformatf("%s[%0d]", NAME, i), \
                              LVALUE[i], \
                              RVALUE[i], \
                              TYPE, \
                              COMPARER) \
    end \
  `m_uvm_compare_end

// uvm_compare_qda_enum
           
`define uvm_compare_qda_enum(LVALUE, RVALUE, TYPE, COMPARER=comparer) \
  `uvm_compare_named_qda_enum(`"LVALUE`", LVALUE, RVALUE, TYPE, COMPARER)

`define uvm_compare_named_qda_enum(NAME, LVALUE, RVALUE, TYPE, COMPARER=comparer) \
  `m_uvm_compare_begin(LVALUE, RVALUE, COMPARER) \
    `uvm_compare_named_int($sformatf("%s.size()", NAME), \
                           LVALUE.size(), \
                           RVALUE.size(), \
                           UVM_DEC, \
                           COMPARER) \
    `uvm_compare_named_sarray_enum(NAME, LVALUE, RVALUE, TYPE, COMPARER) \
  `m_uvm_compare_end

// uvm_compare_sarray_int

`define uvm_compare_sarray_object(LVALUE, RVALUE, POLICY=UVM_DEFAULT_POLICY, COMPARER=comparer) \
  `uvm_compare_named_sarray_object(`"LVALUE`", LVALUE, RVALUE, POLICY, COMPARER)

`define uvm_compare_named_sarray_object(NAME, LVALUE, RVALUE, POLICY=UVM_DEFAULT_POLICY, COMPARER=comparer) \
  `m_uvm_compare_begin(LVALUE, RVALUE, COMPARER) \
    uvm_recursion_policy_enum prev_rec__; \
    prev_rec__ = COMPARER.get_recursion_policy(); \
    if (POLICY != UVM_DEFAULT_POLICY) \
      COMPARER.set_recursion_policy(POLICY); \
    foreach (LVALUE[i]) begin \
      `m_uvm_compare_named_object($sformatf("%s[%0d]", NAME, i), \
                                  LVALUE[i], \
                                  RVALUE[i], \
                                  COMPARER) \
    end \
    if (POLICY != UVM_DEFAULT_POLICY) \
      COMPARER.set_recursion_policy(prev_rec__); \
  `m_uvm_compare_end

// uvm_compare_qda_int
           
`define uvm_compare_qda_object(LVALUE, RVALUE, POLICY=UVM_DEFAULT_POLICY, COMPARER=comparer) \
  `uvm_compare_named_qda_object(`"LVALUE`", LVALUE, RVALUE, POLICY, COMPARER)
    
`define uvm_compare_named_qda_object(NAME, LVALUE, RVALUE, POLICY=UVM_DEFAULT_POLICY, COMPARER=comparer) \
  `m_uvm_compare_begin(LVALUE, RVALUE, COMPARER) \
    `uvm_compare_named_int($sformatf("%s.size()", NAME), \
                           LVALUE.size(), \
                           RVALUE.size(), \
                           UVM_DEC, \
                           COMPARER) \
    `uvm_compare_named_sarray_object(NAME, LVALUE, RVALUE, POLICY, COMPARER) \
  `m_uvm_compare_end

// uvm_compare_sarray_string
           
`define uvm_compare_sarray_string(LVALUE, RVALUE, COMPARER=comparer) \
  `uvm_compare_named_sarray_string(`"LVALUE`", LVALUE, RVALUE, COMPARER)
                  
`define uvm_compare_named_sarray_string(NAME, LVALUE, RVALUE, COMPARER=comparer) \
  `m_uvm_compare_begin(LVALUE, RVALUE, COMPARER) \
    foreach (LVALUE[i]) begin \
      `uvm_compare_named_string($sformatf("%s[%0d]", NAME, i), \
                                LVALUE[i], \
                                RVALUE[i], \
                                COMPARER) \
    end \
  `m_uvm_compare_end

// uvm_compare_qda_string
           
`define uvm_compare_qda_string(LVALUE, RVALUE, COMPARER=comparer) \
  `uvm_compare_named_qda_string(`"LVALUE`", LVALUE, RVALUE, COMPARER)
    
`define uvm_compare_named_qda_string(NAME, LVALUE, RVALUE, COMPARER=comparer) \
  `m_uvm_compare_begin(LVALUE, RVALUE, COMPARER) \
    `uvm_compare_named_int($sformatf("%s.size()", NAME), \
                           LVALUE.size(), \
                           RVALUE.size(), \
                           UVM_DEC, \
                           COMPARER) \
    `uvm_compare_named_sarray_string(NAME, LVALUE, RVALUE, COMPARER) \
  `m_uvm_compare_end
           
// uvm_compare_aa_int_string
           
`define uvm_compare_aa_int_string(LVALUE, RVALUE, RADIX, COMPARER=comparer) \
  `uvm_compare_named_aa_int_string(`"LVALUE`", LVALUE, RVALUE, RADIX, COMPARER)
    
`define uvm_compare_named_aa_int_string(NAME, LVALUE, RVALUE, RADIX, COMPARER=comparer) \
  `m_uvm_compare_begin(LVALUE, RVALUE, COMPARER) \
    foreach(LVALUE[i]) begin \
      if (!RVALUE.exists(i)) begin \
        COMPARER.print_msg($sformatf("%s: Key '%s' not in RHS", NAME, i)); \
      end \
      else begin \
        `uvm_compare_named_int($sformatf("%s[%s]", NAME, i), \
                               LVALUE[i], \
                               RVALUE[i], \
                               RADIX, \
                               COMPARER) \
      end \
    end \
    foreach(RVALUE[i]) begin \
      if(!LVALUE.exists(i)) begin \
        COMPARER.print_msg($sformatf("%s: Key '%s' not in LHS", NAME, i)); \
      end \
    end \
  `m_uvm_compare_end
           
// uvm_compare_aa_object_string
           
`define uvm_compare_aa_object_string(LVALUE, RVALUE, POLICY=UVM_DEFAULT_POLICY, COMPARER=comparer) \
  `uvm_compare_named_aa_object_string(`"LVALUE`", LVALUE, RVALUE, POLICY, COMPARER)
    
`define uvm_compare_named_aa_object_string(NAME, LVALUE, RVALUE, POLICY=UVM_DEFAULT_POLICY, COMPARER=comparer) \
  `m_uvm_compare_begin(LVALUE, RVALUE, COMPARER) \
    uvm_recursion_policy_enum prev_rec__; \
    prev_rec__ = COMPARER.get_recursion_policy(); \
    if (POLICY != UVM_DEFAULT_POLICY) \
      COMPARER.set_recursion_policy(POLICY); \
    foreach(LVALUE[i]) begin \
      if (!RVALUE.exists(i)) begin \
        COMPARER.print_msg($sformatf("%s: Key '%s' not in RHS", NAME, i)); \
      end \
      else begin \
        `m_uvm_compare_named_object($sformatf("%s[%s]", NAME, i), \
                                    LVALUE[i], \
                                    RVALUE[i], \
                                    COMPARER) \
      end \
    end \
    foreach(RVALUE[i]) begin \
      if(!LVALUE.exists(i)) begin \
        COMPARER.print_msg($sformatf("%s: Key '%s' not in LHS", NAME, i)); \
      end \
    end \
    if (POLICY != UVM_DEFAULT_POLICY) \
      COMPARER.set_recursion_policy(prev_rec__); \
  `m_uvm_compare_end

// uvm_compare_aa_string_string
           
`define uvm_compare_aa_string_string(LVALUE, RVALUE, COMPARER=comparer) \
  `uvm_compare_named_aa_string_string(`"LVALUE`", LVALUE, RVALUE, COMPARER)
    
`define uvm_compare_named_aa_string_string(NAME, LVALUE, RVALUE, COMPARER=comparer) \
  `m_uvm_compare_begin(LVALUE, RVALUE, COMPARER) \
    foreach(LVALUE[i]) begin \
      if (!RVALUE.exists(i)) begin \
        COMPARER.print_msg($sformatf("%s: Key '%s' not in RHS", NAME, i)); \
      end \
      else begin \
        `uvm_compare_named_string($sformatf("%s[%s]", NAME, i), \
                                  LVALUE[i], \
                                  RVALUE[i], \
                                  COMPARER) \
      end \
    end \
    foreach(RVALUE[i]) begin \
      if(!LVALUE.exists(i)) begin \
        COMPARER.print_msg($sformatf("%s: Key '%s' not in LHS", NAME, i)); \
      end \
    end \
  `m_uvm_compare_end
           
// uvm_compare_aa_int_int
           
`define uvm_compare_aa_int_int(LVALUE, RVALUE, RADIX, COMPARER=comparer) \
  `uvm_compare_named_aa_int_int(`"LVALUE`", LVALUE, RVALUE, RADIX, COMPARER)
                                                               
`define uvm_compare_named_aa_int_int(NAME, LVALUE, RVALUE, RADIX, COMPARER=comparer) \
  `m_uvm_compare_begin(LVALUE, RVALUE, COMPARER) \
    foreach(LVALUE[i]) begin \
      if (!RVALUE.exists(i)) begin \
        COMPARER.print_msg($sformatf("%s: Key '%0d' not in RHS", NAME, i)); \
      end \
      else begin \
        `uvm_compare_named_int($sformatf("%s[%d]", NAME, i), \
                               LVALUE[i], \
                               RVALUE[i], \
                               RADIX, \
                               COMPARER) \
      end \
    end \
    foreach(RVALUE[i]) begin \
      if(!LVALUE.exists(i)) begin \
        COMPARER.print_msg($sformatf("%s: Key '%0d' not in LHS", NAME, i)); \
      end \
    end \
  `m_uvm_compare_end
           
// uvm_compare_aa_object_int
           
`define uvm_compare_aa_object_int(LVALUE, RVALUE, POLICY=UVM_DEFAULT_POLICY, COMPARER=comparer) \
  `uvm_compare_named_aa_object_int(`"LVALUE`", LVALUE, RVALUE, POLICY, COMPARER)
    
`define uvm_compare_named_aa_object_int(NAME, LVALUE, RVALUE, POLICY=UVM_DEFAULT_POLICY, COMPARER=comparer) \
  `m_uvm_compare_begin(LVALUE, RVALUE, COMPARER) \
    uvm_recursion_policy_enum prev_rec__; \
    prev_rec__ = COMPARER.get_recursion_policy(); \
    if (POLICY != UVM_DEFAULT_POLICY) \
      COMPARER.set_recursion_policy(POLICY); \
    foreach(LVALUE[i]) begin \
      if (!RVALUE.exists(i)) begin \
        COMPARER.print_msg($sformatf("%s: Key '%0d' not in RHS", NAME, i)); \
      end \
      else begin \
        `m_uvm_compare_named_object($sformatf("%s[%s]", NAME, i), \
                                    LVALUE[i], \
                                    RVALUE[i], \
                                    COMPARER) \
      end \
    end \
    foreach(RVALUE[i]) begin \
      if(!LVALUE.exists(i)) begin \
        COMPARER.print_msg($sformatf("%s: Key '%0d' not in LHS", NAME, i)); \
      end \
    end \
    if (POLICY != UVM_DEFAULT_POLICY) \
      COMPARER.set_recursion_policy(prev_rec__); \
  `m_uvm_compare_end

// uvm_compare_aa_string_int
           
`define uvm_compare_aa_string_int(LVALUE, RVALUE, COMPARER=comparer) \
  `uvm_compare_named_aa_string_int(`"LVALUE`", LVALUE, RVALUE, COMPARER)
    
`define uvm_compare_named_aa_string_int(NAME, LVALUE, RVALUE, COMPARER=comparer) \
  `m_uvm_compare_begin(LVALUE, RVALUE, COMPARER) \
    foreach(LVALUE[i]) begin \
      if (!RVALUE.exists(i)) begin \
        COMPARER.print_msg($sformatf("%s: Key '%d' not in RHS", NAME, i)); \
      end \
      else begin \
        `uvm_compare_named_string($sformatf("%s[%d]", NAME, i), \
                                  LVALUE[i], \
                                  RVALUE[i], \
                                  COMPARER) \
      end \
    end \
    foreach(RVALUE[i]) begin \
      if(!LVALUE.exists(i)) begin \
        COMPARER.print_msg($sformatf("%s: Key '%d' not in LHS", NAME, i)); \
      end \
    end \
  `m_uvm_compare_end

`endif // UVM_COMPARER_DEFINES_SVH
