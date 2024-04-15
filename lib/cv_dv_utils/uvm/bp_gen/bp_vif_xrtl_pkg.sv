// ----------------------------------------------------------------------------
//Copyright 2023 CEA*
//*Commissariat a l'Energie Atomique et aux Energies Alternatives (CEA)
//
//Licensed under the Apache License, Version 2.0 (the "License");
//you may not use this file except in compliance with the License.
//You may obtain a copy of the License at
//
//    http://www.apache.org/licenses/LICENSE-2.0
//
//Unless required by applicable law or agreed to in writing, software
//distributed under the License is distributed on an "AS IS" BASIS,
//WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//See the License for the specific language governing permissions and
//limitations under the License.
//[END OF HEADER]
// ----------------------------------------------------------------------------
// ----------------------------------------------------------------------------
//  Description : Package with defines for XRTL portion of bp IF
//                
// 
// ----------------------------------------------------------------------------

package bp_vif_xrtl_pkg;

    parameter bp_txns_per_xfer = 4;

// -------------------------------------------------------------------------
// Enumerations
// -------------------------------------------------------------------------
typedef enum { BP_OFF=0,      // BP OFF - for N, number of indicated clocks
               BP_ON=1,       // BP ON  - for N, number of indicated clocks,
               BP_TOGGLE=2,   // BP toggles every Mth cycles for N clocks
               BP_PERCENT=3 } // BP is asserted M% of the time for N clocks }

                  bp_drive_type_t;

// ----------------------------------------------------------------------
// Simple Struct to hold on Transaction
// ----------------------------------------------------------------------
typedef struct {
       bit             valid;
       bit [1:0]       bp_type;
       bit [19:0]      N;
       bit [7:0]       M;
} driver_single_bp_txn_t;

// ----------------------------------------------------------------------
// Burst of BP Transactions
// ----------------------------------------------------------------------
typedef struct {
       driver_single_bp_txn_t   txns[bp_txns_per_xfer];
} driver_burst_bp_txn_t;


class bp_vif_xrtl;

    // ----------------------------------------------------------------------
    // Events used to tell driver to send more data
    // ----------------------------------------------------------------------
    event done_sending;

    // ----------------------------------------------------------------------
    // Name
    // ----------------------------------------------------------------------
    protected string name;

    // ----------------------------------------------------------------------
    // Constructor
    // ----------------------------------------------------------------------
    function new( string name_in ) ;
        name = name_in;
    endfunction : new


endclass : bp_vif_xrtl


endpackage : bp_vif_xrtl_pkg

