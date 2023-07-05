//
// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
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


`ifndef __UVMA_CV32E40S_CORE_CNTRL_AGENT_SV__
`define __UVMA_CV32E40S_CORE_CNTRL_AGENT_SV__

/**
 * Core control agent defined for the CV32E40S
 */
class uvma_cv32e40s_core_cntrl_agent_c extends uvma_core_cntrl_agent_c;

   string log_tag = "CV32E40SCORECTRLAGT";

   `uvm_component_utils_begin(uvma_cv32e40s_core_cntrl_agent_c)
   `uvm_component_utils_end

   /**
    * Default constructor.
    */
   extern function new(string name="uvma_cv32e40s_core_cntrl_agent", uvm_component parent=null);

   /**
    * Uses uvm_config_db to retrieve cntxt and hand out to sub-components.
    */
   extern virtual function void get_and_set_cntxt();

   /**
    * Uses uvm_config_db to retrieve the Virtual Interface (vif) associated with this
    * agent.
    */
   extern virtual function void retrieve_vif();

   /**
    * Spawn active sequnces
    */
   extern virtual task run_phase(uvm_phase phase);

   /**
    * Spawn fetch enable control sequence
    */
   extern virtual task start_fetch_toggle_seq();

   /**
    * End of elaboration phase
    * Emit ovpsim.ic control file
    */
   extern function void end_of_elaboration_phase(uvm_phase phase);

   /**
    * Configure core specific ISS overrides
    */
   extern function void configure_iss();


endclass : uvma_cv32e40s_core_cntrl_agent_c

function uvma_cv32e40s_core_cntrl_agent_c::new(string name="uvma_cv32e40s_core_cntrl_agent", uvm_component parent=null);

   super.new(name, parent);

   set_inst_override_by_type("driver", uvma_core_cntrl_drv_c::get_type(), uvma_cv32e40s_core_cntrl_drv_c::get_type());

endfunction : new

function void uvma_cv32e40s_core_cntrl_agent_c::retrieve_vif();

   uvma_cv32e40s_core_cntrl_cntxt_c e40s_cntxt;

   $cast(e40s_cntxt, cntxt);

   // Core control interface
   if (!uvm_config_db#(virtual uvme_cv32e40s_core_cntrl_if_t)::get(this, "", $sformatf("core_cntrl_vif"), e40s_cntxt.core_cntrl_vif)) begin
      `uvm_fatal("VIF", $sformatf("Could not find vif handle of type %s in uvm_config_db",
                                    $typename(e40s_cntxt.core_cntrl_vif)))
   end
   else begin
      `uvm_info("VIF", $sformatf("Found vif handle of type %s in uvm_config_db",
                                 $typename(e40s_cntxt.core_cntrl_vif)), UVM_DEBUG)
   end
endfunction : retrieve_vif

function void uvma_cv32e40s_core_cntrl_agent_c::get_and_set_cntxt();

   void'(uvm_config_db#(uvma_core_cntrl_cntxt_c)::get(this, "", "cntxt", cntxt));
   if (!cntxt) begin
      `uvm_info(log_tag, "Context handle is null; creating", UVM_LOW);
      cntxt = uvma_cv32e40s_core_cntrl_cntxt_c::type_id::create("cntxt");
   end

   uvm_config_db#(uvma_core_cntrl_cntxt_c)::set(this, "*", "cntxt", cntxt);

endfunction : get_and_set_cntxt

task uvma_cv32e40s_core_cntrl_agent_c::run_phase(uvm_phase phase);

   if (cfg.is_active) begin
      fork
         start_fetch_toggle_seq();
      join_none
   end

endtask : run_phase

task uvma_cv32e40s_core_cntrl_agent_c::start_fetch_toggle_seq();

  uvme_cv32e40s_fetch_toggle_seq_c fetch_toggle_seq = uvme_cv32e40s_fetch_toggle_seq_c::type_id::create("fetch_toggle_seq");
  void'(fetch_toggle_seq.randomize());
  fetch_toggle_seq.start(this.sequencer);

endtask : start_fetch_toggle_seq

function void uvma_cv32e40s_core_cntrl_agent_c::end_of_elaboration_phase(uvm_phase phase);
  super.end_of_elaboration_phase(phase);

  if (cfg.use_iss) begin
     configure_iss();
  end

endfunction : end_of_elaboration_phase

function void uvma_cv32e40s_core_cntrl_agent_c::configure_iss();
  int    fh;                // file handle ISS control file (typically ovpsim.ic).
  string refpath = "cpu" ;  // root of config path in ISS control file.

  fh = $fopen(cfg.iss_control_file, "a");

  // -------------------------------------------------------------------------------------
  // Parameters
  // -------------------------------------------------------------------------------------

  // Suppress unwanted log messages
  if (cfg.iss_suppress_invalid_msg) begin
    $fwrite(fh, $sformatf("--excludem RISCV_CSR_UNIMP\n"));
    $fwrite(fh, $sformatf("--excludem RISCV_UDEC\n"));
    $fwrite(fh, $sformatf("--excludem RISCV_NFP128\n"));
    $fwrite(fh, $sformatf("--excludem RISCV_NFP16\n"));
    $fwrite(fh, $sformatf("--excludem RISCV_ILL\n"));
  end

  $fwrite(fh, $sformatf("--override %s/misa_Extensions=0x%06x\n", refpath, cfg.get_misa()));
  $fwrite(fh, $sformatf("--override %s/noinhibit_mask=0x%08x\n", refpath, cfg.get_noinhibit_mask()));
  $fwrite(fh, $sformatf("--override %s/Smstateen=T\n", refpath));

  // -------------------------------------------------------------------------------------
  // Boot strap pins
  // -------------------------------------------------------------------------------------
  $fwrite(fh, $sformatf("--override %s/mhartid=%0d\n", refpath, cfg.mhartid));
  $fwrite(fh, $sformatf("--override %s/mimpid=%0d\n", refpath, cfg.mimpid));
  $fwrite(fh, $sformatf("--override %s/startaddress=0x%08x\n", refpath, cfg.boot_addr));
  // Specification forces mtvec[0] high at reset regardless of bootstrap pin state of mtvec_addr_i]0]
  $fwrite(fh, $sformatf("--override %s/mtvec_mask=0xffffff8%1d\n", refpath, (cfg.clic_interrupt_enable ? 0 : 1)));
  $fwrite(fh, $sformatf("--override %s/mtvec=0x%08x\n", refpath, cfg.mtvec_addr | (cfg.clic_interrupt_enable ? 32'b11 : 32'b1)));
  $fwrite(fh, $sformatf("--override %s/nmi_address=0x%08x\n", refpath, cfg.nmi_addr));
  $fwrite(fh, $sformatf("--override %s/debug_address=0x%08x\n", refpath, cfg.dm_halt_addr));
  $fwrite(fh, $sformatf("--override %s/dexc_address=0x%08x\n", refpath, cfg.dm_exception_addr));
  $fwrite(fh, $sformatf("--override %s/extension_*/tdata1_reset=0x%08x\n", refpath, 'h28001000));

  if (cfg.ext_zca_supported) begin
    $fwrite(fh, $sformatf("--override %s/Zca=1\n", refpath));
  end else begin
    $fwrite(fh, $sformatf("--override %s/Zca=0\n", refpath));
  end

  if (cfg.ext_zcb_supported) begin
    $fwrite(fh, $sformatf("--override %s/Zcb=1\n", refpath));
  end else begin
    $fwrite(fh, $sformatf("--override %s/Zcb=0\n", refpath));
  end

  if (cfg.ext_zcmp_supported) begin
    $fwrite(fh, $sformatf("--override %s/Zcmp=1\n", refpath));
  end else begin
    $fwrite(fh, $sformatf("--override %s/Zcmp=0\n", refpath));
  end

  if (cfg.ext_zcmt_supported) begin
    $fwrite(fh, $sformatf("--override %s/Zcmt=1\n", refpath));
  end else begin
    $fwrite(fh, $sformatf("--override %s/Zcmt=0\n", refpath));
  end

  if (cfg.is_ext_b_supported()) begin
     // Bitmanip version
     case (cfg.bitmanip_version)
        BITMANIP_VERSION_0P90:       $fwrite(fh, $sformatf("--override %s/bitmanip_version=0.90\n", refpath));
        BITMANIP_VERSION_0P91:       $fwrite(fh, $sformatf("--override %s/bitmanip_version=0.91\n", refpath));
        BITMANIP_VERSION_0P92:       $fwrite(fh, $sformatf("--override %s/bitmanip_version=0.92\n", refpath));
        BITMANIP_VERSION_0P93:       $fwrite(fh, $sformatf("--override %s/bitmanip_version=0.93\n", refpath));
        BITMANIP_VERSION_0P93_DRAFT: $fwrite(fh, $sformatf("--override %s/bitmanip_version=0.93-draft\n", refpath));
        BITMANIP_VERSION_0P94:       $fwrite(fh, $sformatf("--override %s/bitmanip_version=0.94\n", refpath));
        BITMANIP_VERSION_1P00:       $fwrite(fh, $sformatf("--override %s/bitmanip_version=1.0.0\n", refpath));
     endcase

     // Bitmanip extensions
     $fwrite(fh, $sformatf("--override %s/Zba=%0d\n", refpath, cfg.ext_zba_supported));
     $fwrite(fh, $sformatf("--override %s/Zbb=%0d\n", refpath, cfg.ext_zbb_supported));
     $fwrite(fh, $sformatf("--override %s/Zbc=%0d\n", refpath, cfg.ext_zbc_supported));
     $fwrite(fh, $sformatf("--override %s/Zbe=%0d\n", refpath, cfg.ext_zbe_supported));
     $fwrite(fh, $sformatf("--override %s/Zbf=%0d\n", refpath, cfg.ext_zbf_supported));
     $fwrite(fh, $sformatf("--override %s/Zbm=%0d\n", refpath, cfg.ext_zbm_supported));
     $fwrite(fh, $sformatf("--override %s/Zbp=%0d\n", refpath, cfg.ext_zbp_supported));
     $fwrite(fh, $sformatf("--override %s/Zbr=%0d\n", refpath, cfg.ext_zbr_supported));
     $fwrite(fh, $sformatf("--override %s/Zbs=%0d\n", refpath, cfg.ext_zbs_supported));
     $fwrite(fh, $sformatf("--override %s/Zbt=%0d\n", refpath, cfg.ext_zbt_supported));
  end

   case(cfg.debug_spec_version)
     DEBUG_VERSION_0_13_2: $fwrite(fh, $sformatf("--override %s/debug_version=0.13.2-DRAFT\n", refpath));
     DEBUG_VERSION_0_14_0: $fwrite(fh, $sformatf("--override %s/debug_version=0.14.0-DRAFT\n", refpath));
     DEBUG_VERSION_1_0_0: begin
       $fwrite(fh, $sformatf("--override %s/debug_version=1.0.0-STABLE\n", refpath));
     end
   endcase

   case(cfg.priv_spec_version)
     PRIV_VERSION_MASTER:   $fwrite(fh, $sformatf("--override %s/priv_version=master\n", refpath));
     PRIV_VERSION_1_10:     $fwrite(fh, $sformatf("--override %s/priv_version=1.10\n", refpath));
     PRIV_VERSION_1_11:     $fwrite(fh, $sformatf("--override %s/priv_version=1.11\n", refpath));
     PRIV_VERSION_1_12:     $fwrite(fh, $sformatf("--override %s/priv_version=1.12\n", refpath));
     PRIV_VERSION_20190405: $fwrite(fh, $sformatf("--override %s/priv_version=20190405\n", refpath));
   endcase

   if (cfg.priv_spec_version == PRIV_VERSION_1_12) begin
     case(cfg.endianness)
       ENDIAN_LITTLE, ENDIAN_BIG: $fwrite(fh, $sformatf("--override %s/endianFixed=1\n", refpath));
       ENDIAN_MIXED:              $fwrite(fh, $sformatf("--override %s/endianFixed=0\n", refpath));
     endcase
   end

   // PMA Regions
   $fwrite(fh, $sformatf("--override %s/extension_*/PMA_NUM_REGIONS=%0d\n", refpath, cfg.pma_regions.size()));
   foreach (cfg.pma_regions[i]) begin
      $fwrite(fh, $sformatf("--override %s/extension_*/word_addr_low%0d=0x%08x\n", refpath, i, cfg.pma_regions[i].word_addr_low));
      $fwrite(fh, $sformatf("--override %s/extension_*/word_addr_high%0d=0x%08x\n", refpath, i, cfg.pma_regions[i].word_addr_high));
      $fwrite(fh, $sformatf("--override %s/extension_*/main%0d=%0d\n", refpath, i, cfg.pma_regions[i].main));
      $fwrite(fh, $sformatf("--override %s/extension_*/bufferable%0d=%0d\n", refpath, i, cfg.pma_regions[i].bufferable));
      $fwrite(fh, $sformatf("--override %s/extension_*/cacheable%0d=%0d\n", refpath, i, cfg.pma_regions[i].cacheable));
      $fwrite(fh, $sformatf("--override %s/extension_*/atomic%0d=%0d\n", refpath, i, 1));
   end

   // Enable use of hw reg names instead of abi
   $fwrite(fh, $sformatf("--override %s/use_hw_reg_names=T\n", refpath));
   $fclose(fh);
endfunction : configure_iss

`endif // __UVMA_CV32E40S_CORE_CNTRL_AGENT_SV__
