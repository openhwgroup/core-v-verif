//
// Copyright 2020 OpenHW Group
// Copyright 2020 Silicon Labs, Inc.
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://solderpad.org/licenses/
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

`ifndef __UVME_CV32E40P_RANDOM_DEBUG__
`define __UVME_CV32E40P_RANDOM_DEBUG__

class uvme_cv32e40p_random_debug_c extends uvme_cv32e40p_base_vseq_c;

    rand int dly;

    `uvm_object_utils_begin(uvme_cv32e40p_random_debug_c)
    `uvm_object_utils_end

    constraint default_dly_c {
        dly inside {[1:10000]};
    }

    extern function new(string name="uvme_cv32e40p_random_debug");
    extern virtual task body();
    extern virtual task rand_delay();
endclass : uvme_cv32e40p_random_debug_c

function uvme_cv32e40p_random_debug_c::new(string name="uvme_cv32e40p_random_debug");
    super.new(name);
endfunction : new

task uvme_cv32e40p_random_debug_c::rand_delay();
    if (!this.randomize()) begin
        `uvm_fatal("RAND_DELAY", "Cannot randomize uvme_cv32e40p_random_debug_c")
    end
    #(dly);
endtask : rand_delay

task uvme_cv32e40p_random_debug_c::body();
    fork
        while(1) begin
            uvma_debug_seq_item_c debug_req;
            `uvm_do_on_with(debug_req, p_sequencer.debug_sequencer, {});
            rand_delay();
        end
    join
endtask : body
`endif // __UVME_CV32E40P_RANDOM_DEBUG__
