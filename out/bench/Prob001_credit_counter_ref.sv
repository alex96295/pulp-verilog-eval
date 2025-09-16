// Compiled by morty-0.9.0 / 2025-09-16 17:34:16.39719893 +02:00:00

// Copyright 2020 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Author: Fabian Schuiki <fschuiki@iis.ee.ethz.ch>
// Author: Paul Scheffler <paulsc@iis.ee.ethz.ch>

// Copyright 2018, 2021 ETH Zurich and University of Bologna.
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
// SPDX-License-Identifier: SHL-0.51
//
// Author: Stefan Mach <smach@iis.ee.ethz.ch>
// Description: Common register defines for RTL designs



// Abridged Summary of available FF macros:
// `FF:      asynchronous active-low reset
// `FFAR:    asynchronous active-high reset
// `FFARN:   [deprecated] asynchronous active-low reset
// `FFSR:    synchronous active-high reset
// `FFSRN:   synchronous active-low reset
// `FFNR:    without reset
// `FFL:     load-enable and asynchronous active-low reset
// `FFLAR:   load-enable and asynchronous active-high reset
// `FFLARN:  [deprecated] load-enable and asynchronous active-low reset
// `FFLARNC: load-enable and asynchronous active-low reset and synchronous active-high clear
// `FFLSR:   load-enable and synchronous active-high reset
// `FFLSRN:  load-enable and synchronous active-low reset
// `FFLNR:   load-enable without reset






// Flip-Flop with asynchronous active-low reset
// __q: Q output of FF
// __d: D input of FF
// __reset_value: value assigned upon reset
// (__clk: clock input)
// (__arst_n: asynchronous reset, active-low)


// Flip-Flop with asynchronous active-high reset
// __q: Q output of FF
// __d: D input of FF
// __reset_value: value assigned upon reset
// __clk: clock input
// __arst: asynchronous reset, active-high


// DEPRECATED - use `FF instead
// Flip-Flop with asynchronous active-low reset
// __q: Q output of FF
// __d: D input of FF
// __reset_value: value assigned upon reset
// __clk: clock input
// __arst_n: asynchronous reset, active-low


// Flip-Flop with synchronous active-high reset
// __q: Q output of FF
// __d: D input of FF
// __reset_value: value assigned upon reset
// __clk: clock input
// __reset_clk: reset input, active-high


// Flip-Flop with synchronous active-low reset
// __q: Q output of FF
// __d: D input of FF
// __reset_value: value assigned upon reset
// __clk: clock input
// __reset_n_clk: reset input, active-low


// Always-enable Flip-Flop without reset
// __q: Q output of FF
// __d: D input of FF
// __clk: clock input


// Flip-Flop with load-enable and asynchronous active-low reset (implicit clock and reset)
// __q: Q output of FF
// __d: D input of FF
// __load: load d value into FF
// __reset_value: value assigned upon reset
// (__clk: clock input)
// (__arst_n: asynchronous reset, active-low)


// Flip-Flop with load-enable and asynchronous active-high reset
// __q: Q output of FF
// __d: D input of FF
// __load: load d value into FF
// __reset_value: value assigned upon reset
// __clk: clock input
// __arst: asynchronous reset, active-high


// DEPRECATED - use `FFL instead
// Flip-Flop with load-enable and asynchronous active-low reset
// __q: Q output of FF
// __d: D input of FF
// __load: load d value into FF
// __reset_value: value assigned upon reset
// __clk: clock input
// __arst_n: asynchronous reset, active-low


// Flip-Flop with load-enable and synchronous active-high reset
// __q: Q output of FF
// __d: D input of FF
// __load: load d value into FF
// __reset_value: value assigned upon reset
// __clk: clock input
// __reset_clk: reset input, active-high


// Flip-Flop with load-enable and synchronous active-low reset
// __q: Q output of FF
// __d: D input of FF
// __load: load d value into FF
// __reset_value: value assigned upon reset
// __clk: clock input
// __reset_n_clk: reset input, active-low


// Flip-Flop with load-enable and asynchronous active-low reset and synchronous clear
// __q: Q output of FF
// __d: D input of FF
// __load: load d value into FF
// __clear: assign reset value into FF
// __reset_value: value assigned upon reset
// __clk: clock input
// __arst_n: asynchronous reset, active-low


// Flip-Flop with asynchronous active-low reset and synchronous clear
// __q: Q output of FF
// __d: D input of FF
// __clear: assign reset value into FF
// __reset_value: value assigned upon reset
// __clk: clock input
// __arst_n: asynchronous reset, active-low


// Load-enable Flip-Flop without reset
// __q: Q output of FF
// __d: D input of FF
// __load: load d value into FF
// __clk: clock input




// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Macros and helper code for using assertions.
//  - Provides default clk and rst options to simplify code
//  - Provides boiler plate template for common assertions





///////////////////
// Helper macros //
///////////////////

// helper macro to reduce code clutter, can be used to hide signal defs only used for assertions


   

// forcefully enable assertions with ASSERTS_OVERRIDE_ON, overriding any define that turns them off


// Converts an arbitrary block of code into a Verilog string


// ASSERT_RPT is available to change the reporting mechanism when an assert fails



///////////////////////////////////////
// Simple assertion and cover macros //
///////////////////////////////////////

// Default clk and reset signals used by assertion macros below.



// Immediate assertion
// Note that immediate assertions are sensitive to simulation glitches.


// Assertion in initial block. Can be used for things like parameter checking.


// Assertion in final block. Can be used for things like queues being empty
// at end of sim, all credits returned at end of sim, state machines in idle
// at end of sim.


// Assert a concurrent property directly.
// It can be called as a module (or interface) body item.

// Note: Above we use (__rst !== '0) in the disable iff statements instead of
// (__rst == '1).  This properly disables the assertion in cases when reset is X at
// the beginning of a simulation. For that case, (reset == '1) does not disable the
// assertion.

// Assert a concurrent property NEVER happens


// Assert that signal has a known value (each bit is either '0' or '1') after reset.
// It can be called as a module (or interface) body item.


//  Cover a concurrent property


//////////////////////////////
// Complex assertion macros //
//////////////////////////////

// Assert that signal is an active-high pulse with pulse length of 1 clock cycle


// Assert that a property is true only when an enable signal is set.  It can be called as a module
// (or interface) body item.


// Assert that signal has a known value (each bit is either '0' or '1') after reset if enable is
// set.  It can be called as a module (or interface) body item.


///////////////////////
// Assumption macros //
///////////////////////

// Assume a concurrent property


// Assume an immediate property


//////////////////////////////////
// For formal verification only //
//////////////////////////////////

// Note that the existing set of ASSERT macros specified above shall be used for FPV,
// thereby ensuring that the assertions are evaluated during DV simulations as well.

// ASSUME_FPV
// Assume a concurrent property during formal verification only.


// ASSUME_I_FPV
// Assume a concurrent property during formal verification only.


// COVER_FPV
// Cover a concurrent property during formal verification



 // COMMON_CELLS_ASSERTIONS_SVH


module TopModule #(
  parameter int unsigned NumCredits      = 0,
  /// Whether credit is full or empty on reset
  parameter bit          InitCreditEmpty = 1'b0,
  /// Derived parameters *Do not override*
  parameter int unsigned InitNumCredits  = InitCreditEmpty ? '0 : NumCredits,
  parameter type         credit_cnt_t    = logic [$clog2(NumCredits):0]
) (
  input  logic clk_i,
  input  logic rst_ni,

  output credit_cnt_t credit_o,

  input  logic credit_give_i,
  input  logic credit_take_i,
  input  logic credit_init_i,  // Reinitialize (soft-reset) credit; takes priority

  output logic credit_left_o,
  output logic credit_crit_o,  // Giving one more credit will fill the credits
  output logic credit_full_o
);

  credit_cnt_t credit_d, credit_q;
  logic increment, decrement;

  assign decrement = credit_take_i & ~credit_give_i;
  assign increment = ~credit_take_i & credit_give_i;

  always_comb begin
    credit_d = credit_q;
    if      (decrement) credit_d = credit_q - 1;
    else if (increment) credit_d = credit_q + 1;
  end

      /* synopsys sync_set_reset "credit_init_i" */                   
                                                            
  always_ff @(posedge (clk_i) or negedge (rst_ni)) begin        
    if (!rst_ni) begin                                          
      credit_q <= (InitNumCredits);                                     
    end else begin                                                
      if (credit_init_i) begin                                          
        credit_q <= (InitNumCredits);                                   
      end else begin                                              
        credit_q <= (credit_d);                                             
      end                                                         
    end                                                           
  end

  assign credit_o       = credit_q;
  assign credit_left_o  = (credit_q != '0);
  assign credit_crit_o  = (credit_q == NumCredits-1);
  assign credit_full_o  = (credit_q == NumCredits);

  CreditUnderflow: assert property (@(posedge clk_i) disable iff ((!rst_ni) !== '0) not (credit_o == '0 && decrement))                      
    else begin                                                                                              
      $error("[ASSERT FAILED] [%m] %s: %s (%s:%0d)", "CreditUnderflow", "", "/scratch2/aottaviano/rtlgen-explore/mage/pulp-verilog-eval/assets/common_cells/src/TopModule.sv", 5); 
                                                        
    end                                                                                                     

  CreditOverflow: assert property (@(posedge clk_i) disable iff ((!rst_ni) !== '0) not (credit_o == NumCredits && increment))                      
    else begin                                                                                              
      $error("[ASSERT FAILED] [%m] %s: %s (%s:%0d)", "CreditOverflow", "", "/scratch2/aottaviano/rtlgen-explore/mage/pulp-verilog-eval/assets/common_cells/src/TopModule.sv", 5); 
                                                        
    end                                                                                                     


endmodule
