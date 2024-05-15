

import "DPI-C" function void spike_init();
import "DPI-C" function st_rvfi spike_step();

    function void iss_init();
        spike_init();
    endfunction

    function st_rvfi iss_step();
        st_rvfi rvfi_o;
        rvfi_o = spike_step();
        return rvfi_o;
    endfunction
