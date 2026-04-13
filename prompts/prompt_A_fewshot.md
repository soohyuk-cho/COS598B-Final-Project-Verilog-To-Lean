# Prompt A (Few-Shot) — One-Shot Translation with Examples (Sys A+)

**Usage**: Copy the entire text below (replacing `{{VERILOG}}`) into ChatGPT.
**Purpose**: One-shot translation with a worked example for each schema type.
**System**: Sys A variant in benchmark.
**When to use**: For Tier 2+ modules where one-shot without examples fails.

---

```
You are an expert in both Verilog RTL design and the Lean 4 theorem prover.

Your task is to translate the given Verilog module into a Lean 4 formal model.
Below are two worked examples showing the exact style and schema to follow.

=== EXAMPLE 1: COMBINATIONAL MODULE ===

Verilog:
  module Mux_2_1 (
      input wire in0, in1, sel,
      output wire out
  );
      assign out = sel ? in1 : in0;
  endmodule

Lean 4 output:
  namespace Mux_2_1_01

  abbrev Bit := Bool

  structure Inputs where
    in0 : Bit
    in1 : Bit
    sel : Bit
  deriving Repr, DecidableEq

  structure Outputs where
    out : Bit
  deriving Repr, DecidableEq

  def eval (input : Inputs) : Outputs :=
    { out := if input.sel then input.in1 else input.in0 }

  theorem eval_sel_false (in0 in1 : Bit) :
      eval { in0 := in0, in1 := in1, sel := false } = { out := in0 } := rfl

  theorem eval_sel_true (in0 in1 : Bit) :
      eval { in0 := in0, in1 := in1, sel := true } = { out := in1 } := rfl

  end Mux_2_1_01

=== EXAMPLE 2: SEQUENTIAL MODULE ===

Verilog:
  module counter #(parameter WIDTH = 4) (
      input wire clk, rst, en,
      output reg [WIDTH-1:0] count
  );
      always @(posedge clk) begin
          if (rst)      count <= 0;
          else if (en)  count <= count + 1;
          else          count <= count;
      end
  endmodule

Lean 4 output:
  import Std

  namespace CounterWrap

  def modulus (w : Nat) : Nat := 2 ^ w
  def wrap (w : Nat) (n : Nat) : Nat := n % modulus w

  structure State (w : Nat) where
    count : Nat
  deriving Repr, DecidableEq

  structure Input where
    rst : Bool
    en  : Bool
  deriving Repr, DecidableEq

  structure Output where
    countOut : Nat
  deriving Repr, DecidableEq

  def zeroState (w : Nat) : State w := { count := 0 }

  def step {w : Nat} (s : State w) (i : Input) : State w :=
    if i.rst then zeroState w
    else if i.en then { count := wrap w (s.count + 1) }
    else s

  def out {w : Nat} (s : State w) : Output := { countOut := s.count }

  @[simp] theorem step_reset {w : Nat} (s : State w) (en : Bool) :
      step s { rst := true, en := en } = zeroState w := by simp [step, zeroState]

  @[simp] theorem step_hold {w : Nat} (s : State w) :
      step s { rst := false, en := false } = s := by simp [step]

  @[simp] theorem step_inc {w : Nat} (s : State w) :
      step s { rst := false, en := true } = { count := wrap w (s.count + 1) } := by
    simp [step, wrap]

  end CounterWrap

=== REQUIREMENTS ===
- Do NOT use `sorry`.
- All structures must derive `Repr` and `DecidableEq`.
- Faithfully encode the Verilog semantics (bit widths, priority of if/else, reset value).
- For multi-bit signals, use BitVec with the correct width.
- Theorems must actually typecheck — prefer fewer correct theorems over more theorems with sorry.

=== VERILOG MODULE TO TRANSLATE ===

{{VERILOG}}

=== OUTPUT ===
Produce only the Lean 4 code. No explanation, no markdown fences, just the raw Lean source.
```
