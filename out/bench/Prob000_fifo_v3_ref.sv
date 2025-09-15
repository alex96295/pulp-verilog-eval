// Compiled by morty-0.9.0 / 2025-09-15 15:57:27.195123213 +02:00:00

// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>

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


module fifo_v3 #(
    parameter bit          FALL_THROUGH = 1'b0, // fifo is in fall-through mode
    parameter int unsigned DATA_WIDTH   = 32,   // default data width if the fifo is of type logic
    parameter int unsigned DEPTH        = 8,    // depth can be arbitrary from 0 to 2**32
    parameter type dtype                = logic [DATA_WIDTH-1:0],
    // DO NOT OVERWRITE THIS PARAMETER
    parameter int unsigned ADDR_DEPTH   = (DEPTH > 1) ? $clog2(DEPTH) : 1
)(
    input  logic  clk_i,            // Clock
    input  logic  rst_ni,           // Asynchronous reset active low
    input  logic  flush_i,          // flush the queue
    input  logic  testmode_i,       // test_mode to bypass clock gating
    // status flags
    output logic  full_o,           // queue is full
    output logic  empty_o,          // queue is empty
    output logic  [ADDR_DEPTH-1:0] usage_o,  // fill pointer
    // as long as the queue is not full we can push new data
    input  dtype  data_i,           // data to push into the queue
    input  logic  push_i,           // data is valid and can be pushed to the queue
    // as long as the queue is not empty we can pop new elements
    output dtype  data_o,           // output data
    input  logic  pop_i             // pop head from queue
);
    // local parameter
    // FIFO depth - handle the case of pass-through, synthesizer will do constant propagation
    localparam int unsigned FifoDepth = (DEPTH > 0) ? DEPTH : 1;
    // clock gating control
    logic gate_clock;
    // pointer to the read and write section of the queue
    logic [ADDR_DEPTH - 1:0] read_pointer_n, read_pointer_q, write_pointer_n, write_pointer_q;
    // keep a counter to keep track of the current queue status
    // this integer will be truncated by the synthesis tool
    logic [ADDR_DEPTH:0] status_cnt_n, status_cnt_q;
    // actual memory
    dtype [FifoDepth - 1:0] mem_n, mem_q;

    assign usage_o = status_cnt_q[ADDR_DEPTH-1:0];

    if (DEPTH == 0) begin : gen_pass_through
        assign empty_o     = ~push_i;
        assign full_o      = ~pop_i;
    end else begin : gen_fifo
        assign full_o       = (status_cnt_q == FifoDepth[ADDR_DEPTH:0]);
        assign empty_o      = (status_cnt_q == 0) & ~(FALL_THROUGH & push_i);
    end
    // status flags

    // read and write queue logic
    always_comb begin : read_write_comb
        // default assignment
        read_pointer_n  = read_pointer_q;
        write_pointer_n = write_pointer_q;
        status_cnt_n    = status_cnt_q;
        data_o          = (DEPTH == 0) ? data_i : mem_q[read_pointer_q];
        mem_n           = mem_q;
        gate_clock      = 1'b1;

        // push a new element to the queue
        if (push_i && ~full_o) begin
            // push the data onto the queue
            mem_n[write_pointer_q] = data_i;
            // un-gate the clock, we want to write something
            gate_clock = 1'b0;
            // increment the write counter
            // this is dead code when DEPTH is a power of two
            if (write_pointer_q == FifoDepth[ADDR_DEPTH-1:0] - 1)
                write_pointer_n = '0;
            else
                write_pointer_n = write_pointer_q + 1;
            // increment the overall counter
            status_cnt_n    = status_cnt_q + 1;
        end

        if (pop_i && ~empty_o) begin
            // read from the queue is a default assignment
            // but increment the read pointer...
            // this is dead code when DEPTH is a power of two
            if (read_pointer_n == FifoDepth[ADDR_DEPTH-1:0] - 1)
                read_pointer_n = '0;
            else
                read_pointer_n = read_pointer_q + 1;
            // ... and decrement the overall count
            status_cnt_n   = status_cnt_q - 1;
        end

        // keep the count pointer stable if we push and pop at the same time
        if (push_i && pop_i &&  ~full_o && ~empty_o)
            status_cnt_n   = status_cnt_q;

        // FIFO is in pass through mode -> do not change the pointers
        if (FALL_THROUGH && (status_cnt_q == 0) && push_i) begin
            data_o = data_i;
            if (pop_i) begin
                status_cnt_n = status_cnt_q;
                read_pointer_n = read_pointer_q;
                write_pointer_n = write_pointer_q;
            end
        end
    end

    // sequential process
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if(~rst_ni) begin
            read_pointer_q  <= '0;
            write_pointer_q <= '0;
            status_cnt_q    <= '0;
        end else begin
            if (flush_i) begin
                read_pointer_q  <= '0;
                write_pointer_q <= '0;
                status_cnt_q    <= '0;
             end else begin
                read_pointer_q  <= read_pointer_n;
                write_pointer_q <= write_pointer_n;
                status_cnt_q    <= status_cnt_n;
            end
        end
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if(~rst_ni) begin
            mem_q <= {FifoDepth{dtype'('0)}};
        end else if (!gate_clock) begin
            mem_q <= mem_n;
        end
    end

initial begin                                        
    depth_0: assert (DEPTH > 0)                            
      else begin                                       
        $error("[ASSERT FAILED] [%m] %s: %s (%s:%0d)", "depth_0", "DEPTH must be greater than 0.", "/scratch2/aottaviano/rtlgen-explore/mage/pulp-verilog-eval/assets/common_cells/src/fifo_v3.sv", 5); 
 
      end                                              
  end                                                  


    full_write: assert property (@(posedge clk_i) disable iff ((!rst_ni) !== '0) (full_o |-> ~push_i))                    
    else begin                                                                                        
      $error("[ASSERT FAILED] [%m] %s: %s (%s:%0d)", "full_write", "Trying to push new data although the FIFO is full.", "/scratch2/aottaviano/rtlgen-explore/mage/pulp-verilog-eval/assets/common_cells/src/fifo_v3.sv", 5); 
                                                  
    end                                                                                               


    empty_read: assert property (@(posedge clk_i) disable iff ((!rst_ni) !== '0) (empty_o |-> ~pop_i))                    
    else begin                                                                                        
      $error("[ASSERT FAILED] [%m] %s: %s (%s:%0d)", "empty_read", "Trying to pop data although the FIFO is empty.", "/scratch2/aottaviano/rtlgen-explore/mage/pulp-verilog-eval/assets/common_cells/src/fifo_v3.sv", 5); 
                                                  
    end                                                                                               



endmodule // fifo_v3
