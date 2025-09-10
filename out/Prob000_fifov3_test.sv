// Compiled by morty-0.9.0 / 2025-09-10 13:49:59.055172946 +02:00:00

// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Clock and Reset Generator
module clk_rst_gen #(
  parameter time          ClkPeriod = 0ps, // minimum: 2ps
  parameter int unsigned  RstClkCycles = 0
) (
  output logic clk_o,
  output logic rst_no
);

  logic clk;

  // Clock Generation
  initial begin
    clk = 1'b0;
  end
  always begin
    // Emit rising clock edge.
    clk = 1'b1;
    // Wait for at most half the clock period before emitting falling clock edge.  Due to integer
    // division, this is not always exactly half the clock period but as close as we can get.
    #(ClkPeriod / 2);
    // Emit falling clock edge.
    clk = 1'b0;
    // Wait for remainder of clock period before continuing with next cycle.
    #((ClkPeriod + 1) / 2);
  end
  assign clk_o = clk;

  // Reset Generation
  initial begin
    static int unsigned rst_cnt = 0;
    rst_no = 1'b0;
    #(ClkPeriod / 2); // Start counting clock cycles on first complete cycle.
    while (rst_cnt < RstClkCycles) begin
      @(posedge clk);
      rst_cnt++;
    end
    rst_no = 1'b1;
  end

  // Validate parameters.
initial begin: validate_params
    assert (ClkPeriod >= 2ps)
      else $fatal(1, "The clock period must be at least 2ps!");
      // Reason: Gets divided by two, and some simulators do not support non-integer time steps, so
      // if the time unit is 1ps, this would fail.
    assert (RstClkCycles > 0)
      else $fatal(1, "The number of clock cycles in reset must be greater than 0!");
  end


endmodule
// Copyright (c) 2019 ETH Zurich, University of Bologna
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Package with functions and tasks commonly used in constrained randomized verification
package rand_verif_pkg;

  // Pick a random number from the interval [min, max] and wait for that number of clock cyles.
  task automatic rand_wait(input int unsigned min, max, ref logic clk);
      int unsigned rand_success, cycles;
      rand_success = std::randomize(cycles) with {
          cycles >= min;
          cycles <= max;
      };
      assert (rand_success) else $error("Failed to randomize wait cycles!");
      repeat (cycles) @(posedge clk);
  endtask

endpackage
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
// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Testbench for generic FIFO
module fifo_inst_tb #(
    // FIFO parameters
    parameter bit           FALL_THROUGH,
    parameter int unsigned  DEPTH,
    parameter int unsigned  DATA_WIDTH = 8,
    // TB parameters
    parameter int unsigned  N_CHECKS,
    parameter time          TA,
    parameter time          TT
) (
    input  logic    clk_i,
    input  logic    rst_ni,
    output logic    done_o
);

    import rand_verif_pkg::rand_wait;

    typedef logic [DATA_WIDTH-1:0] data_t;

    logic           clk,
                    flush,
                    full,
                    empty,
                    push,
                    pop,
                    try_push,
                    try_pop;

    data_t          wdata,
                    rdata;

    int unsigned    n_checks = 0;

    assign clk = clk_i;

    fifo_v3 #(
        .FALL_THROUGH   ( FALL_THROUGH  ),
        .DATA_WIDTH     ( DATA_WIDTH    ),
        .DEPTH          ( DEPTH         )
    ) dut (
        .clk_i,
        .rst_ni,
        .flush_i        ( flush         ),
        .testmode_i     ( 1'b0          ),
        .full_o         ( full          ),
        .empty_o        ( empty         ),
        .usage_o        (               ),
        .data_i         ( wdata         ),
        .push_i         ( push          ),
        .data_o         ( rdata         ),
        .pop_i          ( pop           )
    );

    // Simulation information and stopping.
    // TODO: Better stop after certain coverage is reached.
    initial begin
        done_o = 1'b0;
        $display("%m: Running test with FALL_THROUGH=%0d, DEPTH=%0d", FALL_THROUGH, DEPTH);
        wait (n_checks >= N_CHECKS);
        done_o = 1'b1;
        $display("%m: Checked %0d stimuli", n_checks);
    end

    class random_action_t;
        rand logic [1:0] action;
        constraint random_action {
            action dist {
                0 := 40,
                1 := 40,
                3 := 2,
                0 := 0
            };
        }
    endclass

    // Input driver: push, wdata, and flush
    assign push = try_push & ~full;
    initial begin
        automatic random_action_t rand_act = new();
        flush       <= 1'b0;
        wdata       <= 'x;
        try_push    <= 1'b0;
        wait (rst_ni);
        forever begin
            static logic rand_success;
            rand_wait(1, 8, clk);
            rand_success = rand_act.randomize(); assert(rand_success);
            case (rand_act.action)
                0: begin // new random data and try to push
                    wdata       <= #TA $random();
                    try_push    <= #TA 1'b1;
                end
                1: begin // new random data but do not try to push
                    wdata       <= #TA $random();
                    try_push    <= #TA 1'b0;
                end
                2: begin // flush
                    flush       <= #TA 1'b1;
                    rand_wait(1, 8, clk);
                    flush       <= #TA 1'b0;
                end
            endcase
        end
    end

    // Output driver: pop
    assign pop = try_pop & ~empty;
    initial begin
        try_pop <= 1'b0;
        wait (rst_ni);
        forever begin
            rand_wait(1, 8, clk);
            try_pop <= #TA $random();
        end
    end

    // Monitor & checker: model expected response and check against actual response
    initial begin
        data_t queue[$];
        wait (rst_ni);
        forever begin
            @(posedge clk_i);
            #(TT);
            if (flush) begin
                queue = {};
            end else begin
                if (push && !full) begin
                    queue.push_back(wdata);
                end
                if (pop && !empty) begin
                    automatic data_t data = queue.pop_front();
                    assert (rdata == data) else $error("Queue output %0x != %0x", rdata, data);
                    n_checks++;
                end
            end
        end
    end

// https://github.com/verilator/verilator/issues/5981
if (FALL_THROUGH) begin
        // In fall through mode, assert that the output data is equal to the input data when pushing
        // to an empty FIFO.
        assert property (@(posedge clk_i) ((empty & ~push) ##1 push) |-> rdata == wdata)
            else $error("Input did not fall through");
    end


endmodule

// Testbench for different FIFO configurations
module fifo_tb #(
    // TB parameters
    parameter int unsigned  N_CHECKS        = 100000,
    parameter time          TCLK            = 10ns,
    parameter time          TA              = TCLK * 1/4,
    parameter time          TT              = TCLK * 3/4
);

    logic       clk,
                rst_n;

    logic [5:0] done;

    clk_rst_gen #(.ClkPeriod(TCLK), .RstClkCycles(10)) i_clk_rst_gen (
        .clk_o    (clk),
        .rst_no   (rst_n)
    );

    fifo_inst_tb #(
        .FALL_THROUGH   (1'b0),
        .DEPTH          (8),
        .N_CHECKS       (N_CHECKS),
        .TA             (TA),
        .TT             (TT)
    ) i_tb_8 (
        .clk_i  (clk),
        .rst_ni (rst_n),
        .done_o (done[0])
    );

    fifo_inst_tb #(
        .FALL_THROUGH   (1'b1),
        .DEPTH          (8),
        .N_CHECKS       (N_CHECKS),
        .TA             (TA),
        .TT             (TT)
    ) i_tb_ft_8 (
        .clk_i  (clk),
        .rst_ni (rst_n),
        .done_o (done[1])
    );

    fifo_inst_tb #(
        .FALL_THROUGH   (1'b0),
        .DEPTH          (1),
        .N_CHECKS       (N_CHECKS),
        .TA             (TA),
        .TT             (TT)
    ) i_tb_1 (
        .clk_i  (clk),
        .rst_ni (rst_n),
        .done_o (done[2])
    );

    fifo_inst_tb #(
        .FALL_THROUGH   (1'b1),
        .DEPTH          (1),
        .N_CHECKS       (N_CHECKS),
        .TA             (TA),
        .TT             (TT)
    ) i_tb_ft_1 (
        .clk_i  (clk),
        .rst_ni (rst_n),
        .done_o (done[3])
    );

    fifo_inst_tb #(
        .FALL_THROUGH   (1'b0),
        .DEPTH          (9),
        .N_CHECKS       (N_CHECKS),
        .TA             (TA),
        .TT             (TT)
    ) i_tb_9 (
        .clk_i  (clk),
        .rst_ni (rst_n),
        .done_o (done[4])
    );

    fifo_inst_tb #(
        .FALL_THROUGH   (1'b1),
        .DEPTH          (9),
        .N_CHECKS       (N_CHECKS),
        .TA             (TA),
        .TT             (TT)
    ) i_tb_ft_9 (
        .clk_i  (clk),
        .rst_ni (rst_n),
        .done_o (done[5])
    );

    initial begin
        wait ((&done));
        $finish();
    end

endmodule
