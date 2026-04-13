# Prompt A — One-Shot Translation (Sys A)

**Usage**: Copy the entire text below (replacing `{{VERILOG}}`) into ChatGPT.
**Purpose**: Direct one-shot Verilog → Lean translation with no examples.
**System**: Sys A in benchmark.

---

```
You are an expert in both Verilog RTL design and the Lean 4 theorem prover.

Your task is to translate the given Verilog module into a Lean 4 formal model
following the exact schema described below.

=== LEAN 4 TARGET SCHEMA ===

For COMBINATIONAL modules (no clocked always block):

  namespace <ModuleName>_01

  -- Type abbreviations: use Bool for 1-bit signals, BitVec N for N-bit signals
  abbrev Bit := Bool
  abbrev BitsN := BitVec N

  structure Inputs where
    <field> : <type>
    ...
  deriving Repr, DecidableEq

  structure Outputs where
    <field> : <type>
    ...
  deriving Repr, DecidableEq

  -- Optional: helper constructors for BitVec literals
  def bvN (n : Nat) : BitsN := BitVec.ofNat N n

  -- Evaluation function (required, must be named `eval`)
  def eval (input : Inputs) : Outputs := ...

  -- Theorems: at least one per branch/case, use native_decide or rfl
  theorem <name> : eval { ... } = { ... } := by native_decide

  end <ModuleName>_01

For SEQUENTIAL modules (has clocked always @(posedge clk) block):

  import Std

  namespace <ModuleName>

  structure State ... deriving Repr, DecidableEq   -- internal registers
  structure Input ... deriving Repr, DecidableEq   -- input ports (no clk/rst in struct if rst is handled in step)
  structure Output ... deriving Repr, DecidableEq  -- output ports

  def init : State := ...  -- reset state

  -- Transition function: encode the Verilog always block priority exactly
  -- (e.g., if rst has highest priority, check it first)
  def step (s : State) (i : Input) : State := ...

  -- Output function: pure function from state to outputs
  def out (s : State) : Output := ...

  -- Theorems with @[simp]:
  -- Cover reset, hold (no enable), each operation, priority ordering
  @[simp] theorem step_reset ... := by simp [step, init]
  @[simp] theorem step_hold  ... := by simp [step]
  ...

  end <ModuleName>

=== REQUIREMENTS ===
- Do NOT use `sorry` anywhere.
- Only use API available for Lean 4.29
- All structures must derive `Repr` and `DecidableEq`.
- The namespace must match the Verilog module name.
- Faithfully encode Verilog semantics (bit widths, priority of if/else, reset value).
- For multi-bit signals, use BitVec with the correct width.
- For wrap-around counters, use modular arithmetic (% 2^w).
- Theorems must actually compile — do not write theorems you are not confident about.
  If unsure, write fewer theorems rather than using sorry.
- Do not add clk to the Input structure; model clocked behavior with the step function.

=== VERILOG MODULE TO TRANSLATE ===

{{VERILOG}}

=== OUTPUT ===
Produce only the Lean 4 code. No explanation, no markdown fences, just the raw Lean source.
```
