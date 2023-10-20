#include "Proc.h"
#include "disasm.h"

namespace openhw
{
    st_rvfi Processor::step(size_t n)
    {
        st_rvfi rvfi;
        rvfi.insn = 0; rvfi.pc_rdata = 0;
        rvfi.rd1_addr = 0; rvfi.rd1_wdata = 0;
        rvfi.rs1_addr = 0; rvfi.rs1_rdata = 0;
        rvfi.rs2_addr = 0; rvfi.rs2_rdata = 0;

        this->taken_trap = false;

        rvfi.pc_rdata = this->get_state()->pc;
        processor_t::step(n);
        rvfi.mode = this->get_state()->last_inst_priv;
        rvfi.insn = (uint32_t) (this->get_state()->last_inst_fetched.bits() & 0xffffffffULL);

        // TODO FIXME Handle multiple/zero writes in a single insn.
        auto& reg_commits = this->get_state()->log_reg_write;
        int xlen = this->get_state()->last_inst_xlen;
        int flen = this->get_state()->last_inst_flen;

        rvfi.rs1_addr = this->get_state()->last_inst_fetched.rs1();
        // TODO add rs1_value
        rvfi.rs2_addr = this->get_state()->last_inst_fetched.rs2();
        // TODO add rs2_value

        bool got_commit = false;
        for (auto& reg : reg_commits) {

            if (!got_commit) {
                rvfi.rd1_addr = reg.first >> 4;
                if (rvfi.rd1_addr > 32) continue;
                // TODO FIXME Take into account the XLEN/FLEN for int/FP values.
                rvfi.rd1_wdata = reg.second.v[0];
                // TODO FIXME Handle multiple register commits per cycle.
                // TODO FIXME This must be handled on the RVFI side as well.
                got_commit = true; // FORNOW Latch only the first commit.
            }
        }

        // Remove sign extension applied by Spike in 32b mode.
        if (this->get_xlen() == 32) {
            rvfi.pc_rdata &= 0xffffffffULL;
            rvfi.rd1_wdata &= 0xffffffffULL;
        }

        // TODO FIXME There's no direct access to the exception status anymore.
        //commit_log.was_exception = this->get_state()->was_exception;
        rvfi.trap = this->taken_trap;
        rvfi.cause = this->which_trap;

        return rvfi;
    }

    Processor::Processor(const isa_parser_t *isa, const cfg_t* cfg,
        simif_t* sim, uint32_t id, bool halt_on_reset,
        FILE *log_file, std::ostream& sout_,
        Params& params) // because of command line option --log and -s we need both
      :  processor_t::processor_t(isa, cfg, sim, id, halt_on_reset, log_file, sout_)
    {

        this->params.set("/top/core/0/", "isa", any(std::string("RV32GC")));
        this->params.set("/top/core/0/", "boot_addr", any(0x80000000UL));
        this->params.set("/top/core/0/", "mmu_mode", any(std::string("sv39")));
        this->params.set("/top/core/0/", "misa", any(""));
        this->params.set("/top/core/0/", "pmpaddr0", any(0x0UL));
        this->params.set("/top/core/0/", "pmpcfg0", any(0x0UL));
        this->params.set("/top/core/0/", "marchid", any(0x3UL));
        this->params.set("/top/core/0/", "mvendorid", any(0x00000602UL));

        // Process User Params
        ParseParams("/top/core/0/", this->params, params);

        string isa_str = std::any_cast<string>(this->params["/top/core/0/isa"]);
        this->isa = (const isa_parser_t*) new isa_parser_t (isa_str.c_str(), DEFAULT_PRIV);

        disassembler = new disassembler_t(isa);
        for (auto e : isa->get_extensions())
            register_extension(e.second);

        this->reset();

        uint64_t new_pc = std::any_cast<uint64_t>(this->params["/top/core/0/boot_addr"]);
        this->state.pc = new_pc;

        this->put_csr(CSR_PMPADDR0, std::any_cast<uint64_t>(this->params["/top/core/0/pmpaddr0"]));
        this->put_csr(CSR_PMPCFG0, std::any_cast<uint64_t>(this->params["/top/core/0/pmpcfg0"]));

        this->put_csr(CSR_MVENDORID, std::any_cast<uint64_t>(this->params["/top/core/0/mvendorid"]));
        this->put_csr(CSR_MARCHID, std::any_cast<uint64_t>(this->params["/top/core/0/marchid"]));
    }

    void Processor::take_trap(trap_t& t, reg_t epc)
    {
        this->taken_trap = true;
        this->which_trap = t.cause();
        processor_t::take_trap(t, epc);
    }

}
