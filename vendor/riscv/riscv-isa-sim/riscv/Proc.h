
#include "Types.h"
#include "processor.h"

namespace openhw
{
    class Processor : public processor_t
    {
        public:
            Processor(const isa_parser_t *isa, const cfg_t* cfg,
                simif_t* sim, uint32_t id, bool halt_on_reset,
                FILE *log_file, std::ostream& sout_, Params& params); // because of command line option --log and -s we need both
            st_rvfi step(size_t n);
            void initParams();
        protected:
            bool taken_trap;
            uint8_t which_trap;
            virtual void take_trap(trap_t& t, reg_t epc); // take an exception

    };

}
