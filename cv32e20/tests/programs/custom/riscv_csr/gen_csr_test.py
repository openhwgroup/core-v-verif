"""
Copyright 2019 Google LLC

Copyright 2023 Intrinsix

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Parse processor-specific CSR description YAML file and generate a CSR test file.
This test code will utilize every CSR instruction, writing values to the CSR
and then using a prediction function to calculate a reference value that will
be written into another register and compared against the value actually stored
in the CSR at this point, allowing for the test to self-check in order to
determine success or failure.
"""

"""
To install the bitstring library:
  1) sudo apt-get install python3-bitstring OR
  2) pip install bitstring
"""

import sys
import yaml
import argparse
import random
import copy
from lib import *

try:
    from bitstring import BitArray as bitarray
except ImportError as e:
    logging.error(
        "Please install bitstring package: sudo apt-get install python3-bitstring")
    sys.exit(RET_FAIL)

"""
Defines the test's success/failure values, one of which will be written to
the chosen signature address to indicate the test's result.
"""
TEST_RESULT = 1
TEST_PASS = 123456789
TEST_FAIL = 1
PRIVILEGE_MODES =  ["DRO", "DRW", "MRO", "MRW",  "HRO", "HRW", "SRO", "SRW","URO", "URW"]
PRIVILEGE_LEVELS = {'D' : 4, 'M' : 3, 'H' : 2, 'S' : 1, 'U' :0}
INTERRUPT_CSRS   =  ["mtvec", "mepc", "mstatus", "mcause", "mtval"]

class SimpleWriteCSRField:
    def __init__(self, mask_bitarray, pos, read_only):
        self.mask_bitarray = mask_bitarray
        self.pos = pos
        self.read_only = read_only

    def write(self, new_field_val, csr_val):
        # only write if not read only
        if not self.read_only:
            val_slice = new_field_val[self.pos[0]:self.pos[1] + 1]
            csr_val.overwrite(self.mask_bitarray & val_slice, self.pos[0])

class LegalizeWriteCSRField:
    def __init__(self, mask_bitarray, pos, read_only, legalize_py):
        self.mask_bitarray = mask_bitarray
        self.pos = pos
        self.read_only = read_only
        self.legalize_py = legalize_py

    def write(self, new_field_val, csr_val):
        # only write if not read only
        if not self.read_only:
            val_new_slice = new_field_val[self.pos[0]:self.pos[1] + 1]
            val_orig_slice = csr_val[self.pos[0]:self.pos[1] + 1]

            legal_val_new = self._legalize_val(val_new_slice.uint, val_orig_slice.uint)
            val_slice = bitarray(uint=legal_val_new,
                length=self.pos[1] - self.pos[0] + 1)

            csr_val.overwrite(self.mask_bitarray & val_slice, self.pos[0])

    def _legalize_val(self, val_in, val_orig):
        legalize_globals = {
                'val_orig': val_orig,
                'val_in' : val_in,
                'val_out' : val_in
        }

        exec(self.legalize_py, legalize_globals)

        return legalize_globals['val_out']


def get_csr_map(csr_file, xlen):
    """
    Parses the YAML file containing CSR descriptions.

    Args:
      csr_file: The CSR YAML file.
      xlen: The current RISC-V ISA bit length.

    Returns:
      A dictionary contining mappings for each CSR, of the form:
      { csr_name : [csr_address, csr_val_bitarray, csr_write_fields, csr_read_mask_bitarray] }
    """
    rv_string = "rv{}".format(str(xlen))
    csrs = {}
    with open(csr_file, "r") as c:
        csr_description = yaml.safe_load(c)
        for csr_dict in csr_description:
            csr_name = csr_dict.get("csr")
            csr_address = csr_dict.get("address")
            assert csr_address, "No address for csr {}".format(csr_name)
            assert (rv_string in csr_dict), "The {} CSR must be configured for rv{}".format(
                csr_name, str(rv))
            csr_value = bitarray(uintbe=0, length=xlen)
            csr_write_fields = []
            csr_read_mask = bitarray(uintbe=0, length=xlen)
            csr_field_list = csr_dict.get(rv_string)
            csr_is_volatile = csr_dict.get("volatile")
            csr_privilege_mode = csr_dict.get("privilege_mode")
            assert (csr_privilege_mode in PRIVILEGE_MODES), "Invalid privilege mode {} for csr {}".format(
                csr_name, csr_privilege_mode)
            csr_skip_me = csr_dict.get("SKIP_ME")
            for csr_field_detail_dict in csr_field_list:
                field_type = csr_field_detail_dict.get("type")
                field_val = csr_field_detail_dict.get("reset_val")
                field_msb = csr_field_detail_dict.get("msb")
                field_lsb = csr_field_detail_dict.get("lsb")
                field_size = field_msb - field_lsb + 1
                if field_type != "WPRI":
                    val_bitarray = bitarray(uint=field_val, length=field_size)
                    mask_bitarray = bitarray(uint=1, length=1) * field_size
                    start_pos = xlen - 1 - field_msb
                    end_pos = xlen - 1 - field_lsb
                    csr_read_mask.overwrite(mask_bitarray, xlen - 1 - field_msb)
                    csr_value.overwrite(val_bitarray, xlen - 1 - field_msb)
                    read_only = True if field_type == "R" else False
                    if field_type == "WARL" and 'warl_legalize' in csr_field_detail_dict:
                        csr_write_fields.append(LegalizeWriteCSRField(mask_bitarray,
                            (start_pos, end_pos), read_only,
                            csr_field_detail_dict['warl_legalize']))
                    else:
                        csr_write_fields.append(SimpleWriteCSRField(mask_bitarray,
                            (start_pos, end_pos), read_only))

            csrs.update({csr_name: [csr_address, csr_value, csr_write_fields,
                                    csr_read_mask, csr_privilege_mode, csr_is_volatile, csr_skip_me]})
    return csrs


def get_rs1_val(iteration, xlen):
    """
    Calculates and returns the 3 test RS1 values that will be used
    to exercise the CSR.

    Args:
      iteration: Integer between 0 and 2 inclusive, indicates which
                 test value to return.
      xlen: The currnet RISC-V ISA bit length.

    Returns:
      A bitarray encoding the value that will be written to the CSR to test it.
      Will be one of 3 values:
        1) 0xa5a5...
        2) 0x5a5a...
        3) A randomly generated number
    """
    if iteration == 0:
        return bitarray(hex="0x{}".format('a5' * int(xlen / 8)))
    elif iteration == 1:
        return bitarray(hex="0x{}".format('5a' * int(xlen / 8)))
    elif iteration == 2:
        val = bitarray(uint=0, length=xlen)
        # Must randomize all 32 bits, due to randomization library limitations
        for i in range(32):
            bit = random.randint(0, 1)
            val.set(bit, i)
        return val


def csr_write(val, csr_val, csr_write_fields):
    """
    Performs a CSR write.

    Args:
      val: A bitarray containing the value to be written.
      csr_val: A bitarray containing the current CSR value.
      csr_write_fields: A list of the CSR's write fields.
    """
    for write_field in csr_write_fields:
        write_field.write(val, csr_val)

"""
CSR Read:
  Reads the given CSR, after applying the bitmask
"""


def csr_read(csr_val, csr_read_mask):
    """
    Performs a CSR read.

    Args:
      csr_val: A bitarray containing the current CSR value.
      csr_read_mask: A bitarray containing the CSR's read mask.

    Returns:
      A bitarray of the logical AND of csr_val and csr_read_mask.
    """
    return csr_val & csr_read_mask


def predict_csr_val(csr_op, rs1_val, csr_val, csr_write_fields, csr_read_mask):
    """
    Predicts the CSR reference value, based on the current CSR operation.

    Args:
      csr_op: A string of the CSR operation being performed.
      rs1_val: A bitarray containing the value to be written to the CSR.
      csr_val: A bitarray containing the current value of the CSR.
      csr_write_field: A list containing the CSR's write fields.
      csr_read_mask: A bitarray containing the CSR's read mask

    Returns:
      A hexadecimal string of the predicted CSR value.
    """
    prediction = None
    # create a zero bitarray to zero extend immediates
    zero = bitarray(uint=0, length=csr_val.len - 5)
    prediction = csr_read(csr_val, csr_read_mask)
    if csr_op == 'csrrw':
        csr_write(rs1_val, csr_val, csr_write_fields)
    elif csr_op == 'csrrs':
        csr_write(rs1_val | prediction, csr_val, csr_write_fields)
    elif csr_op == 'csrrc':
        csr_write((~rs1_val) & prediction, csr_val, csr_write_fields)
    elif csr_op == 'csrrwi':
        zero.append(rs1_val[-5:])
        csr_write(zero, csr_val, csr_write_fields)
    elif csr_op == 'csrrsi':
        zero.append(rs1_val[-5:])
        csr_write(zero | prediction, csr_val, csr_write_fields)
    elif csr_op == 'csrrci':
        zero.append(rs1_val[-5:])
        csr_write((~zero) & prediction, csr_val, csr_write_fields)
    return "0x{}".format(prediction.hex)

def add_auto_gen_comment(test_file, csr_file):
    """
    Adds a comment to the file saying it's auto generated.

    Args:
      test_file: the file the comment is to added to.
      csr_file:  the file name of the yaml file used to generate the test file.
    """
    test_file.write("/* This is an auto-generated file not intended to be hand edited.\n")
    test_file.write(" * Changes should be made by editing the yaml file {}\n".format(csr_file))
    test_file.write(" * Then invoking {} to regenerate this file.\n */\n".format(__file__))
               


def gen_setup(test_file):
    """
    Generates the setup code for the CSR test.

    Args:
      test_file: the file containing the generated assembly code.
    """
    test_file.write(".macro init\n")
    test_file.write(".endm\n")
    test_file.write(".option norvc\n")


def gen_check_writeable_csr(test_file, source_reg, dest_reg, csr_instructions, xlen,
                            csr_address, csr_val, csr_write_fields, csr_read_mask,
                            csr_is_volatile):
    """
    Writes self checking code for accesses to a writable CSR. Writes randomly generated
    values into the CSR and reads back the data.  Does not expect any exceptions to occur.

    Args: 
      test_file:        File to write the code to. 
      source_reg:       Register used to store the value to be written to the CSR and
                        the expected read value. 
      dest_reg:         Register used to store the value read from the CSR
      csr_instructions: List of CSR access instructions to be tested. 
      xlen:             ISA width, passed from command line. 
      The following come direclty from the yaml file: 
      csr_address:      The address of the CSR, as an integer.
      csr_val:          The reset value for this csr. Used by the predict_csr_val funciton.
      csr_write_fields: A list of the CSR's fields. Used by the predict_csr_val funciton.
      csr_read_mask:    A bitarray of readable fields. Used by the predict_csr_val funciton.
      csr_is_volatile:  Boolean value.  If set, no data checking will be done.    
    """
    reset_val = copy.deepcopy(csr_val)
    
    for op in csr_instructions:
        for i in range(3):
            # hex string
            rand_rs1_val = get_rs1_val(i, xlen)
            if op[-1] == "i":
                first_li = ""
                imm = rand_rs1_val[-5:]
                csr_inst = "\t{} {}, {}, 0b{}\n".format(op,
                                                        dest_reg,
                                                        hex(csr_address),
                                                        imm.bin)
                imm_val = bitarray(uint=0, length=xlen - 5)
                imm_val.append(imm)
                predict_li = ("\tli {}, "
                              "{}\n".format(source_reg,
                                            predict_csr_val(op,
                                                            imm_val,
                                                            csr_val,
                                                            csr_write_fields,
                                                            csr_read_mask)))
            else:
                first_li = "\tli {}, 0x{}\n".format(source_reg,
                                                    rand_rs1_val.hex)
                csr_inst = "\t{} {}, {}, {}\n".format(op, dest_reg,
                                                      hex(csr_address),
                                                      source_reg)
                predict_li = ("\tli {}, "
                              "{}\n".format(source_reg,
                                            predict_csr_val(op,
                                                            rand_rs1_val,
                                                            csr_val,
                                                            csr_write_fields,
                                                            csr_read_mask)))
            if (csr_is_volatile):
                branch_check = ""
            else:
                branch_check = "\tbne {}, {}, csr_mismatch\n".format( source_reg, dest_reg)
            test_file.write(first_li)
            test_file.write(csr_inst)
            test_file.write(predict_li)
            test_file.write(branch_check)
    test_file.write("\tli {}, {}\n".format(source_reg, reset_val))
    test_file.write("\tcsrw {}, {}\n".format(hex(csr_address),source_reg))
            
def gen_check_read_only_csr(test_file,  source_reg, dest_reg, csr_instructions, xlen,
                            csr_address, csr_val, csr_write_fields, csr_read_mask,
                            csr_is_volatile):
    """
    Writes self checking code for accesses to a read only CSR. All write accesses
    should result in an exception.  The code written assumes that the address of a 
    global variable used to flag expected illegal instructions is already loaded in 
    register t1 (x6). It also assumes that the exception handler will advance the PC
    past the unconditional branch to error code that it will place after the illegal access.

    Args: 
      test_file:        File to write the code to. 
      source_reg:       Register used to store the value to be written to the CSR and
                        the expected read value. 
      dest_reg:         Register used to store the value read from the CSR
      csr_instructions: List of CSR access instructions to be tested. 
      xlen:             ISA width, passed from command line. 
      The following come direclty from the yaml file: 
      csr_address:      The address of the CSR, as an integer.
      csr_val:          The reset value for this csr. Used by the predict_csr_valf funciton.
      csr_write_fields: A list of the CSR's fields. Used by the predict_csr_valf funciton.
      csr_read_mask:    A bitarray of readable fields. Used by the predict_csr_valf funciton.
      csr_is_volatile:  Boolean value.  If set, no data checking will be done.    
    """
    for op in csr_instructions:
        for i in range(3):
            # hex string
            rand_rs1_val =  bitarray(hex="0x{}".format('00' *int (xlen/8)))
            if (op[4] == 'w'):
                test_file.write("\tlw t0, 0(t1)\n")
                test_file.write("\taddi t0, t0, 1\n")
                test_file.write("\tsw t0, 0(t1)\n") 
            if op[-1] == "i":
                imm = rand_rs1_val[-5:]
                csr_inst = "\t{} {}, {}, 0b{}\n".format(op,
                                                        dest_reg,
                                                        hex(csr_address),
                                                        imm.bin)
                imm_val = bitarray(uint=0, length=xlen - 5)
                imm_val.append(imm)
                predict_li = ("\tli {}, "
                              "{}\n".format(source_reg,
                                            predict_csr_val(op,
                                                            imm_val,
                                                            csr_val,
                                                            csr_write_fields,
                                                            csr_read_mask)))
            else:
                csr_inst = "\t{} {}, {},0x0\n".format(op, dest_reg,
                                                      hex(csr_address))
                predict_li = ("\tli {}, "
                              "{}\n".format(source_reg,
                                            predict_csr_val(op,
                                                            rand_rs1_val,
                                                            csr_val,
                                                            csr_write_fields,
                                                            csr_read_mask)))
            if (csr_is_volatile):
                branch_check = ""
            else:
                branch_check = "\tbne {}, {}, csr_mismatch\n".format( source_reg, dest_reg)
            test_file.write(csr_inst)
            if (op[4] != 'w'):
                test_file.write(predict_li)
                test_file.write(branch_check)
            else:
                test_file.write("\tj csr_user_unauth\n")     

def gen_check_inaccessible_csr(test_file,  source_reg, dest_reg, csr_instructions, xlen,
                            csr_address):
    """
    Writes self checking code for accesses to inaccessilbe CSRs.  Every attempted access
    should result in an exception.  The code written assumes that the address of a 
    global variable used to flag expected illegal instructions is already loaded in 
    register t1 (x6). It also assumes that the exception handler will advance the PC
    past the unconditional branch to error code that it will place after the illegal access.

    Args: 
      test_file:        File to write the code to. 
      source_reg:       Register used to store the value to be written to the CSR and
                        the expected read value. 
      dest_reg:         Register used to store the value read from the CSR
      csr_instructions: List of CSR access instructions to be tested. 
      xlen:             ISA width, passed from command line. 
      The following come direclty from the yaml file: 
      csr_address:      The address of the CSR, as an integer. 
    """
     
    for op in csr_instructions:
        rand_rs1_val = get_rs1_val(0, xlen)
        if op[-1] == "i":
            imm = rand_rs1_val[-5:]
            csr_inst = "\t{} {}, {}, 0b{}\n".format(op,
                                                    dest_reg,
                                                    hex(csr_address),
                                                    imm.bin)
        else:
            csr_inst = "\t{} {}, {}, {}\n".format(op, dest_reg,
                                                  hex(csr_address),
                                                  source_reg)
        test_file.write("\tlw t0, 0(t1)\n")
        test_file.write("\taddi t0, t0, 1\n")
        test_file.write("\tsw t0, 0(t1)\n")
        test_file.write(csr_inst)
        test_file.write("\tj csr_user_unauth\n")

def gen_interrupt_csr_check_func(test_file, header_file, original_csr_map, csr_instructions, xlen):
    """
    Generates a function to check the interrupt related CSRs.  This is done by calling 
    gen_check_writeable_csr on each CSR named in the global list INTERRUPT_CSRS. 
 
    The value placed in mtvec by the C startup code is preserved by this funciton. 

    This allows the interrupt related CSR's to be checked, but still allows for exception
    related features to be exercised in machine mode. 

    Args:
      test_file:        File to write assembly test code out to.
      header_file:      File to write C headers to. 
      original_csr_map: The dictionary containing CSR mappings generated by get_csr_map()
      csr_instructions: A list of all supported CSR instructions in string form.
      xlen:             The RISC-V ISA bit length.
    """
    csr_map = copy.deepcopy(original_csr_map)
    source_reg = "x12"
    dest_reg   = "x13"    
    test_file.write(".globl interrupt_csr_check\n")
    test_file.write("interrupt_csr_check:\n")
    header_file.write("void interrupt_csr_check();\n")
    for csr in INTERRUPT_CSRS:
        csr_address, csr_val, csr_write_fields, csr_read_mask, csr_privilege_mode, \
            csr_is_volatile, csr_skip_me = csr_map.get( csr)    
        test_file.write("\t# {}\n".format(csr)) 
        if (csr_skip_me): 
            test_file.write("\t# \tCSR marked SKIP_ME: {}\n".format(csr_skip_me))
            continue     
        test_file.write("\tli a1, {}\n".format(hex(csr_address))) 
        if (csr == "mtvec"):
            test_file.write("\tli t0, {}\n".format(csr_val)) 
            test_file.write("\tcsrrw t1, {}, t0\n".format(hex(csr_address)))
        gen_check_writeable_csr(test_file,  source_reg, dest_reg,csr_instructions, xlen,
                                csr_address, csr_val, csr_write_fields, csr_read_mask,
                                csr_is_volatile)
        if (csr == "mtvec"):
            test_file.write("\tcsrrw t0, {}, t1\n".format(hex(csr_address)))
                
    test_file.write("\tret\n");
        

def gen_csr_check_func(test_file, header_file, original_csr_map, csr_instructions, xlen,
                       function_name, privilege):
    
    """
    Generates a function to check CSR accesses.  This is done by calling 
    gen_check_writeable_csr, gen_check_read_only_csr, or gen_check_inaccessible_csr
    as approriate based on the privilege leve of the CSR and the privilege 
    level being tested.   
 
    Machine and debug level will skip testing CSR's in the global INTERRUPT_CSR list;
    This allows exception to be taken during the function without worrying about 
    the exception related CSR's chaning in ways that are difficult to predict. These
    CSR's should be tested using the function generated by gen_interrupt_csr_check_func 
    above. 

    This function is coded to handle all possible privilege levels, but only Machine and User 
    are actually used by this script. 

    Args:
      test_file:        File to write assembly test code out to.
      header_file:      File to write C headers to. 
      original_csr_map: The dictionary containing CSR mappings generated by get_csr_map()
      csr_instructions: A list of all supported CSR instructions in string form.
      xlen:             The RISC-V ISA bit length.
      fucntion_name:    The name of the function to create. 
      privilege:        A single character indicating the privilege level to test.
    """
    csr_map = copy.deepcopy(original_csr_map)
    source_reg = "x12"
    dest_reg   = "x13"
    csr_list = list(csr_map.keys())
    test_file.write(".globl {}\n".format(function_name))
    test_file.write("{}:".format(function_name))
    header_file.write("void {}();\n".format(function_name))
    test_file.write("\tla t1, glb_expect_illegal_insn\n")
    for csr in csr_list:
        #Skip interrupt CSR's if they could legitamately be changed.
        if (csr in INTERRUPT_CSRS) and (PRIVILEGE_LEVELS[privilege] >= PRIVILEGE_LEVELS['M']):
            continue;
        csr_address, csr_val, csr_write_fields, csr_read_mask, csr_privilege_mode, \
            csr_is_volatile, csr_skip_me = csr_map.get( csr)
        test_file.write("\t# {}\n".format(csr))
        
        if (csr_skip_me): 
            test_file.write("\t# \tCSR marked SKIP_ME: {}\n".format(csr_skip_me))
            continue
        test_file.write("\tli a1, {}\n".format(hex(csr_address)))
        if (PRIVILEGE_LEVELS[privilege] < PRIVILEGE_LEVELS[csr_privilege_mode[0]]):
            gen_check_inaccessible_csr(test_file, source_reg, dest_reg, csr_instructions, xlen,
                                       csr_address) 
        elif ( csr_privilege_mode[-2:] == "RO"):
            gen_check_read_only_csr(test_file, source_reg, dest_reg, csr_instructions, xlen,
                                    csr_address, csr_val, csr_write_fields, csr_read_mask,
                                    csr_is_volatile)
        else:
            gen_check_writeable_csr(test_file,  source_reg, dest_reg,csr_instructions, xlen,
                                    csr_address, csr_val, csr_write_fields, csr_read_mask,
                                    csr_is_volatile)
     
    test_file.write("\tret\n"); 


def gen_csr_check_unimplemented(test_file, header_file, original_csr_map):
    
    """
    Generates a function to that verifies that no CSR accesses are possible
    to CSR address not listed int the .yaml file.
    
    This function will do a read access to every possible address not listed
    in the .yaml file, setting the glbl_expect_illegal_insn for each one
    and branching to csr_bad_impl if the exectption is not taken. 

    CSR address with the "SKIP_ME" entry in the .yaml file will not be accessed
    by this function. 

    Args:
      test_file:        File to write assembly test code out to.
      header_file:      File to write C headers to. 
      original_csr_map: The dictionary containing CSR mappings generated by get_csr_map()
    """
    csr_map = copy.deepcopy(original_csr_map)
    csr_addrs = list()
    csr_list = list(csr_map.keys())
    test_file.write(".globl csr_check_unimplemented\n")
    test_file.write("csr_check_unimplemented:\n")
    header_file.write("void csr_check_unimplemented();\n")
    for csr in csr_list:
        csr_address, csr_val, csr_write_fields, csr_read_mask, csr_privilege_mode, \
            csr_is_volatile, csr_skip_me = csr_map.get( csr)
        csr_addrs.append(csr_address)
    test_file.write("\tla t1, glb_expect_illegal_insn\n")
    test_file.write("\taddi sp, sp, -4\n")
    test_file.write("\tsw ra, 0(sp)\n")
    for addr in range (0x1000):
        if (addr in csr_addrs):
            continue
        else :       
            test_file.write("\tli a1, {}\n".format(hex(addr))) 
            test_file.write("\tlw t0, 0(t1)\n")
            test_file.write("\taddi t0, t0, 1\n")
            test_file.write("\tsw t0, 0(t1)\n")
            test_file.write("\tcsrr t0, {}\n".format(hex(addr)))
            test_file.write("\tjal ra, csr_bad_impl\n")
    
    test_file.write("\tlw ra, 0(sp)\n") 
    test_file.write("\taddi sp, sp, 4\n")
    test_file.write("\tret\n"); 
            
        
    
def main():
    """Main entry point of CSR test generation script.
     Will set up a list of all supported CSR instructions,
     and seed the RNG."""

    # define command line arguments
    parser = argparse.ArgumentParser()
    parser.add_argument("--csr_file", type=str,
                        default="yaml/csr_template.yaml",
                        help="The YAML file contating descriptions of all processor supported CSRs")
    parser.add_argument("--xlen", type=int, default=32,
                        help="Specify the ISA width, e.g. 32 or 64 or 128")
    parser.add_argument("--iterations", type=int, default=1,
                        help="Specify how many tests to be generated")
    parser.add_argument("--out", type=str, default="./",
                        help="Specify output directory")
    parser.add_argument("--end_signature_addr", type=str, default="0",
                        help="Address that should be written to at end of this test")
    parser.add_argument("--seed", type=int, default=None,
                        help="""Value used to seed the random number generator. If no value is passed in,
                  the RNG will be seeded from an internal source of randomness.""")
    args = parser.parse_args()

    """All supported CSR operations"""
    csr_ops = ['csrrw', 'csrrs', 'csrrc', 'csrrwi', 'csrrsi', 'csrrci']

    """
    Seed the RNG.
    If args.seed is None, seed will be drawn from some internal random source.
    If args.seed is defined, this will be used to seed the RNG for user reproducibility.
    """
    random.seed(args.seed)
    csr_map = get_csr_map(args.csr_file, args.xlen)
    csr_test_file   =  open("{}/riscv_csr_test_{}.S".format(args.out, 0), "w")
    add_auto_gen_comment(csr_test_file, args.csr_file)
    csr_header_file =  open("{}/riscv_csr_test_{}.h".format(args.out, 0), "w")
    add_auto_gen_comment(csr_header_file, args.csr_file)
    
    gen_setup(csr_test_file)
    gen_interrupt_csr_check_func(csr_test_file, csr_header_file,
                                 csr_map, csr_ops, args.xlen)
    gen_csr_check_func(csr_test_file, csr_header_file,
                       csr_map, csr_ops, args.xlen, "machine_mode_check", 'M')
    gen_csr_check_unimplemented(csr_test_file, csr_header_file,csr_map)
    gen_csr_check_func(csr_test_file, csr_header_file,
                       csr_map, csr_ops, args.xlen, "user_mode_check", 'U')
    csr_test_file.close()
    csr_header_file.close()
        
if __name__ == "__main__":
    main()
