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

`ifndef UVM_PACKER_DEFINES_SVH
 `define UVM_PACKER_DEFINES_SVH

//------------------------------------------------------------------------------
//
// MACROS for uvm_packer usage
//
// Provides a set of packing/unpacking macros that will call appropriate methods
// inside of a uvm_packer object.
//
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
// Group -- NODOCS -- Packing Macros
//
// The packing macros assist users who implement the <uvm_object::do_pack>
// method. They help ensure that the pack operation is the exact inverse of the
// unpack operation. See also <Unpacking Macros>.
//
//| virtual function void do_pack(uvm_packer packer);
//|   `uvm_pack_int(cmd)
//|   `uvm_pack_int(addr)
//|   `uvm_pack_array(data)
//| endfunction
//
// The 'N' versions of these macros take a explicit size argument, which must
// be compile-time constant value greater than 0.
//------------------------------------------------------------------------------

//--------------------------------
// Group -- NODOCS -- Packing - With Size Info
//--------------------------------

// Macro -- NODOCS -- `uvm_pack_intN
//
// Pack an integral variable.
//
//| `uvm_pack_intN(VAR,SIZE)
//

// @uvm-ieee 1800.2-2017 auto B.2.4.1
`define uvm_pack_intN(VAR,SIZE) \
  begin \
    bit __array[]; \
    { << bit { __array}} = VAR; \
    __array = new [SIZE] (__array); \
    packer.pack_bits(__array, SIZE); \
  end

// @uvm-ieee 1800.2-2017 auto B.2.4.2
`define uvm_pack_enumN(VAR,SIZE) \
   `uvm_pack_intN(VAR,SIZE)



// @uvm-ieee 1800.2-2017 auto B.2.4.3
`define uvm_pack_sarrayN(VAR,SIZE) \
    begin \
    foreach (VAR `` [index]) \
      `uvm_pack_intN(VAR[index],SIZE) \
    end



// @uvm-ieee 1800.2-2017 auto B.2.4.4
`define uvm_pack_arrayN(VAR,SIZE) \
    begin \
      `uvm_pack_intN(VAR.size(),32) \
      `uvm_pack_sarrayN(VAR,SIZE) \
    end



// @uvm-ieee 1800.2-2017 auto B.2.4.5
`define uvm_pack_queueN(VAR,SIZE) \
   `uvm_pack_arrayN(VAR,SIZE)


//------------------------------
// Group -- NODOCS -- Packing - No Size Info
//------------------------------


// @uvm-ieee 1800.2-2017 auto B.2.4.6
`define uvm_pack_int(VAR) \
   `uvm_pack_intN(VAR,$bits(VAR))

// uvm_pack_object
`define uvm_pack_object(VAR) \
  packer.pack_object(VAR);

// @uvm-ieee 1800.2-2017 auto B.2.4.7
`define uvm_pack_enum(VAR) \
   `uvm_pack_enumN(VAR,$bits(VAR))



// @uvm-ieee 1800.2-2017 auto B.2.4.8
`define uvm_pack_string(VAR) \
  packer.pack_string(VAR);



// @uvm-ieee 1800.2-2017 auto B.2.4.9
`define uvm_pack_real(VAR) \
  packer.pack_real(VAR);



// @uvm-ieee 1800.2-2017 auto B.2.4.10
`define uvm_pack_sarray(VAR)  \
   `uvm_pack_sarrayN(VAR,$bits(VAR[0]))



// @uvm-ieee 1800.2-2017 auto B.2.4.11
`define uvm_pack_array(VAR) \
   `uvm_pack_arrayN(VAR,$bits(VAR[0]))

`define uvm_pack_da(VAR) \
  `uvm_pack_array(VAR)

// @uvm-ieee 1800.2-2017 auto B.2.4.12
`define uvm_pack_queue(VAR) \
   `uvm_pack_queueN(VAR,$bits(VAR[0]))

//------------------------------------------------------------------------------
// Group -- NODOCS -- Unpacking Macros
//
// The unpacking macros assist users who implement the <uvm_object::do_unpack>
// method. They help ensure that the unpack operation is the exact inverse of
// the pack operation. See also <Packing Macros>.
//
//| virtual function void do_unpack(uvm_packer packer);
//|   `uvm_unpack_enum(cmd,cmd_t)
//|   `uvm_unpack_int(addr)
//|   `uvm_unpack_array(data)
//| endfunction
//
// The 'N' versions of these macros take a explicit size argument, which must
// be a compile-time constant value greater than 0.
//------------------------------------------------------------------------------

//----------------------------------
// Group -- NODOCS -- Unpacking - With Size Info
//----------------------------------


// @uvm-ieee 1800.2-2017 auto B.2.5.1
`define uvm_unpack_intN(VAR,SIZE) \
  begin \
    bit __array[] = new [SIZE]; \
    packer.unpack_bits(__array, SIZE); \
    __array = new [$bits(VAR)] (__array); \
    VAR = { << bit { __array }}; \
  end



// @uvm-ieee 1800.2-2017 auto B.2.5.2
`define uvm_unpack_enumN(VAR,SIZE,TYPE) \
  begin \
    bit __array[] = new [SIZE]; \
    packer.unpack_bits(__array, SIZE); \
    __array = new [$bits(VAR)] (__array); \
    VAR = TYPE'({ << bit { __array }}); \
  end



// @uvm-ieee 1800.2-2017 auto B.2.5.3
`define uvm_unpack_sarrayN(VAR,SIZE) \
    begin \
    foreach (VAR `` [i]) \
      `uvm_unpack_intN(VAR``[i], SIZE) \
    end



// @uvm-ieee 1800.2-2017 auto B.2.5.4
`define uvm_unpack_arrayN(VAR,SIZE) \
    begin \
      int sz__; \
      `uvm_unpack_intN(sz__,32) \
      VAR = new[sz__]; \
      `uvm_unpack_sarrayN(VAR,SIZE) \
    end



// @uvm-ieee 1800.2-2017 auto B.2.5.5
`define uvm_unpack_queueN(VAR,SIZE) \
    begin \
      int sz__; \
      `uvm_unpack_intN(sz__,32) \
      while (VAR.size() > sz__) \
        void'(VAR.pop_back()); \
      for (int i=0; i<sz__; i++) \
        `uvm_unpack_intN(VAR[i],SIZE) \
    end


//--------------------------------
// Group -- NODOCS -- Unpacking - No Size Info
//--------------------------------



// @uvm-ieee 1800.2-2017 auto B.2.5.6
`define uvm_unpack_int(VAR) \
   `uvm_unpack_intN(VAR,$bits(VAR))

// uvm_unpack_object
`define uvm_unpack_object(VAR) \
  if (packer.is_null()) begin \
    VAR = null; \
    packer.unpack_object(VAR); \
  end \
  else if (VAR == null) \
    `uvm_error("UVM/PACK/NULL_MACRO", \
               {"Can't unpack '", \
                `"VAR`", \
                "', into a null."}) \
  else \
    packer.unpack_object(VAR);




// @uvm-ieee 1800.2-2017 auto B.2.5.7
`define uvm_unpack_enum(VAR,TYPE) \
   `uvm_unpack_enumN(VAR,$bits(VAR),TYPE)



// @uvm-ieee 1800.2-2017 auto B.2.5.8
`define uvm_unpack_string(VAR) \
  VAR = packer.unpack_string();


// @uvm-ieee 1800.2-2017 auto B.2.5.9
`define uvm_unpack_real(VAR) \
  VAR = packer.unpack_real();



// @uvm-ieee 1800.2-2017 auto B.2.5.10
`define uvm_unpack_sarray(VAR)  \
   `uvm_unpack_sarrayN(VAR,$bits(VAR[0]))



// @uvm-ieee 1800.2-2017 auto B.2.5.11
`define uvm_unpack_array(VAR) \
   `uvm_unpack_arrayN(VAR,$bits(VAR[0]))

// Implementation artifact.  Simplifies field macros.
`define uvm_unpack_da(VAR) \
  `uvm_unpack_array(VAR)


// @uvm-ieee 1800.2-2017 auto B.2.5.12
`define uvm_unpack_queue(VAR) \
   `uvm_unpack_queueN(VAR,$bits(VAR[0]))


//--

`define uvm_pack_aa_int_intN(VAR, SIZE) \
begin \
  `uvm_pack_intN(VAR.num(), 32) \
  if (VAR.num()) begin \
    `uvm_pack_intN(SIZE, 32) \
    foreach(VAR[i]) begin \
      `uvm_pack_intN(i, SIZE) \
      `uvm_pack_int(VAR[i]) \
    end \
  end \
end

`define uvm_unpack_aa_int_intN(VAR, SIZE) \
begin \
  int __num__; \
  `uvm_unpack_intN(__num__, 32) \
  if (__num__ == 0) \
    VAR.delete(); \
  else begin \
    bit[SIZE-1:0] __index__; \
    int __sz__; \
    `uvm_unpack_intN(__sz__, 32) \
    if (SIZE != __sz__) \
      `uvm_error("UVM/UNPACK/AA_INT_SZ", $sformatf("Unpack size '%0d' different from pack size '%0d'", \
                                                   SIZE, \
                                                   __sz__)) \
    for (int __i__ = 0; __i__ < __num__; __i__++) begin \
      `uvm_unpack_intN(__index__, SIZE) \
      `uvm_unpack_int(VAR[__index__]) \
    end \
  end \
end
   
//--

`define uvm_pack_aa_object_intN(VAR, SIZE) \
begin \
  packer.pack_field_int(VAR.num(), 32); \
  if (VAR.num()) begin \
    packer.pack_field_int(SIZE, 32); \
    foreach(VAR[i]) begin \
      `uvm_pack_intN(i, SIZE) \
      `uvm_pack_object(VAR[i]) \
    end \
  end \
end

`define uvm_unpack_aa_object_intN(VAR, SIZE) \
begin \
  int __num__; \
  `uvm_unpack_intN(__num__, 32) \
  if (__num__ == 0) \
    VAR.delete(); \
  else begin \
    bit[SIZE-1:0] __index__; \
    int __sz__; \
    `uvm_unpack_intN(__sz__, 32) \
    if (SIZE != __sz__) \
      `uvm_error("UVM/UNPACK/AA_INT_SZ", $sformatf("Size '%d' insufficient to store '%d' bits", \
                                                   SIZE, \
                                                   __sz__)) \
    for (int __i__ = 0; __i__ < __num__; __i__++) begin \
      `uvm_unpack_intN(__index__, __sz__) \
      `uvm_unpack_object(VAR[__index__]) \
    end \
  end \
end
   
//--

`define uvm_pack_aa_string_intN(VAR, SIZE) \
begin \
  packer.pack_field_int(VAR.num(), 32); \
  if (VAR.num()) begin \
    packer.pack_field_int(SIZE, 32); \
    foreach(VAR[i]) begin \
      `uvm_pack_intN(i, SIZE) \
      `uvm_pack_string(VAR[i]) \
    end \
  end \
end

`define uvm_unpack_aa_string_intN(VAR, SIZE) \
begin \
  int __num__; \
  `uvm_unpack_intN(__num__, 32) \
  if (__num__ == 0) \
    VAR.delete(); \
  else begin \
    bit[SIZE-1:0] __index__; \
    int __sz__; \
    `uvm_unpack_intN(__sz__, 32) \
    if (SIZE != __sz__) \
      `uvm_error("UVM/UNPACK/AA_INT_SZ", $sformatf("Size '%d' insufficient to store '%d' bits", \
                                                   SIZE, \
                                                   __sz__)) \
    for (int __i__ = 0; __i__ < __num__; __i__++) begin \
      `uvm_unpack_intN(__index__, __sz__) \
      `uvm_unpack_string(VAR[__index__]) \
    end \
  end \
end
   
//--

`define uvm_pack_aa_object_string(VAR) \
begin \
  packer.pack_field_int(VAR.num(), 32); \
  if (VAR.num()) begin \
    foreach(VAR[i]) begin \
      `uvm_pack_string(i) \
      `uvm_pack_object(VAR[i]) \
    end \
  end \
end

`define uvm_unpack_aa_object_string(VAR) \
begin \
  int __num__ = packer.unpack_field_int(32); \
  if (__num__ == 0) \
    VAR.delete(); \
  else begin \
    string __index__; \
    for (int __i__ = 0; __i__ < __num__; __i__++) begin \
      `uvm_unpack_string(__index__) \
      `uvm_unpack_object(VAR[__index__]) \
    end \
  end \
end

//--

`define uvm_pack_aa_int_string(VAR) \
begin \
  packer.pack_field_int(VAR.num(), 32); \
  if (VAR.num()) begin \
    foreach(VAR[i]) begin \
      `uvm_pack_string(i) \
      `uvm_pack_int(VAR[i]) \
    end \
  end \
end

`define uvm_unpack_aa_int_string(VAR) \
begin \
  int __num__ = packer.unpack_field_int(32); \
  if (__num__ == 0) \
    VAR.delete(); \
  else begin \
    string __index__; \
    for (int __i__ = 0; __i__ < __num__; __i__++) begin \
      `uvm_unpack_string(__index__) \
      `uvm_unpack_int(VAR[__index__]) \
    end \
  end \
end

//--

`define uvm_pack_aa_string_string(VAR) \
begin \
  packer.pack_field_int(VAR.num(), 32); \
  if (VAR.num()) begin \
    foreach(VAR[i]) begin \
      `uvm_pack_string(i) \
      `uvm_pack_string(VAR[i]) \
    end \
  end \
end

`define uvm_unpack_aa_string_string(VAR) \
begin \
  int __num__ = packer.unpack_field_int(32); \
  if (__num__ == 0) \
    VAR.delete(); \
  else begin \
    string __index__; \
    for (int __i__ = 0; __i__ < __num__; __i__++) begin \
      `uvm_unpack_string(__index__) \
      `uvm_unpack_string(VAR[__index__]) \
    end \
  end \
end

//--

`define uvm_pack_aa_int_enum(VAR, TYPE) \
begin \
  packer.pack_field_int(VAR.num(), 32); \
  if (VAR.num()) begin \
    foreach(VAR[i]) begin \
      `uvm_pack_enum(i) \
      `uvm_pack_int(VAR[i]) \
    end \
  end \
end

`define uvm_unpack_aa_int_enum(VAR, TYPE) \
begin \
  int __num__ = packer.unpack_field_int(32); \
  if (__num__ == 0) \
    VAR.delete(); \
  else begin \
    TYPE __index__; \
    for (int __i__ = 0; __i__ < __num__; __i__++) begin \
      `uvm_unpack_enum(__index__, TYPE) \
      `uvm_unpack_int(VAR[__index__]) \
    end \
  end \
end
   
//--

`define uvm_pack_aa_object_enum(VAR, TYPE) \
begin \
  packer.pack_field_int(VAR.num(), 32); \
  if (VAR.num()) begin \
    foreach(VAR[i]) begin \
      `uvm_pack_enum(i) \
      `uvm_pack_object(VAR[i]) \
    end \
  end \
end

`define uvm_unpack_aa_object_enum(VAR, TYPE) \
begin \
  int __num__ = packer.unpack_field_int(32); \
  if (__num__ == 0) \
    VAR.delete(); \
  else begin \
    TYPE __index__; \
    for (int __i__ = 0; __i__ < __num__; __i__++) begin \
      `uvm_unpack_enum(__index__, TYPE) \
      `uvm_unpack_object(VAR[__index__]) \
    end \
  end \
end
   
//--

`define uvm_pack_aa_string_enum(VAR, TYPE) \
begin \
  packer.pack_field_int(VAR.num(), 32); \
  if (VAR.num()) begin \
    foreach(VAR[i]) begin \
      `uvm_pack_intN(i, SIZE) \
      `uvm_pack_string(VAR[i]) \
    end \
  end \
end

`define uvm_unpack_aa_string_enum(VAR, TYPE) \
begin \
  int __num__ = packer.unpack_field_int(32); \
  if (__num__ == 0) \
    VAR.delete(); \
  else begin \
    TYPE __index__; \
    for (int __i__ = 0; __i__ < __num__; __i__++) begin \
      `uvm_unpack_enum(__index__, TYPE) \
      `uvm_unpack_string(VAR[__index__]) \
    end \
  end \
end
   
//--

`define uvm_pack_sarray_real(VAR) \
  foreach(VAR[index]) \
    `uvm_pack_real(VAR[index])

`define m_uvm_pack_qda_real(VAR) \
  `uvm_pack_intN(VAR.size(), 32) \
  `uvm_pack_sarray_real(VAR)

`define uvm_pack_queue_real(VAR) \
  `m_uvm_pack_qda_real(VAR)

`define uvm_pack_da_real(VAR) \
  `m_uvm_pack_qda_real(VAR)

`define uvm_unpack_sarray_real(VAR) \
  foreach(VAR[index]) \
    `uvm_unpack_real(VAR[index])

`define uvm_unpack_da_real(VAR) \
  begin \
    int tmp_size__; \
    `uvm_unpack_intN(tmp_size__, 32) \
    VAR = new [tmp_size__]; \
    `uvm_unpack_sarray_real(VAR) \
  end

`define uvm_unpack_queue_real(VAR) \
  begin \
    int tmp_size__; \
    `uvm_unpack_intN(tmp_size__, 32) \
    while (VAR.size() > tmp_size__) \
      void'(VAR.pop_back()); \
    for (int i = 0; i < tmp_size__; i++) \
      `uvm_unpack_real(VAR[i]) \
  end

`endif //  `ifndef UVM_PACKER_DEFINES_SVH
