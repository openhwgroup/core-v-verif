// Copyright 2023 Silicon Labs. Inc.
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


`ifndef __UVME_CV32E40S_WU_WFE_NOISE_VSEQ_C__
`define __UVME_CV32E40S_WU_WFE_NOISE_VSEQ_C__

/**
  *
  */
class uvme_cv32e40s_wu_wfe_noise_vseq_c extends uvme_cv32e40s_base_vseq_c;

   rand int unsigned initial_delay_assert;
   rand int unsigned initial_delay_deassert;

   rand int unsigned short_delay_wgt;
   rand int unsigned medium_delay_wgt;
   rand int unsigned long_delay_wgt;

   semaphore asserted_wu;
   semaphore deasserted_wu;
  `uvm_object_utils_begin(uvme_cv32e40s_wu_wfe_noise_vseq_c);
  `uvm_object_utils_end

   constraint default_delay_c {
     soft short_delay_wgt == 2;
     soft medium_delay_wgt == 5;
     soft long_delay_wgt == 3;
   }

   constraint valid_initial_delay_assert_c {
     initial_delay_assert dist { 0 :/ 2,
                                 [10:500] :/ 4,
                                 [500:1000] :/ 3};
   }

   constraint valid_initial_delay_deassert_c {
     initial_delay_deassert dist { 0 :/ 2,
                                   [10:500] :/ 4,
                                   [500:1000] :/ 3};
   }

  extern function new(string name = "");

  extern virtual task body();

  extern virtual task rand_delay();

endclass : uvme_cv32e40s_wu_wfe_noise_vseq_c

function uvme_cv32e40s_wu_wfe_noise_vseq_c::new(string name = "");
  super.new(name);
endfunction : new

task uvme_cv32e40s_wu_wfe_noise_vseq_c::rand_delay();
  randcase
    short_delay_wgt:  repeat($urandom_range(100, 1))       @(cntxt.wfe_wu_cntxt.vif.drv_cb);
    medium_delay_wgt: repeat($urandom_range(500, 100))     @(cntxt.wfe_wu_cntxt.vif.drv_cb);
    long_delay_wgt:   repeat($urandom_range(10_000, 5000)) @(cntxt.wfe_wu_cntxt.vif.drv_cb);
  endcase
endtask : rand_delay

task uvme_cv32e40s_wu_wfe_noise_vseq_c::body();
  asserted_wu   = new(1);
  deasserted_wu = new(1);

  // start with deasserted
  void'(asserted_wu.put(1));

  fork
    begin : gen_assert
      repeat (initial_delay_assert) @(cntxt.wfe_wu_cntxt.vif.drv_cb);

      forever begin
        @(cntxt.wfe_wu_cntxt.vif.drv_cb)
        if (deasserted_wu.try_get(1)) begin
          uvma_wfe_wu_seq_item_c wfe_req;

          `uvm_do_on_with(wfe_req, p_sequencer.wfe_wu_sequencer, {
            action == UVMA_WFE_WU_SEQ_ITEM_ACTION_ASSERT;
          })
          rand_delay();
          asserted_wu.put(1);
        end
      end
    end

    begin : gen_deassert
      repeat (initial_delay_deassert) @(cntxt.wfe_wu_cntxt.vif.drv_cb);

      forever begin
        @(cntxt.wfe_wu_cntxt.vif.drv_cb)
        if (asserted_wu.try_get(1)) begin
          uvma_wfe_wu_seq_item_c wfe_req;

          `uvm_do_on_with(wfe_req, p_sequencer.wfe_wu_sequencer, {
            action == UVMA_WFE_WU_SEQ_ITEM_ACTION_DEASSERT;
          })
          rand_delay();
          deasserted_wu.put(1);
        end
      end
    end
  join

endtask : body

`endif // __UVME_CV32E40S_WU_WFE_NOISE_VSEQ_C__

