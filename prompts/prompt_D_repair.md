# Prompt D — Iterative Repair (Sys D)

**Usage**: Use this after an initial translation attempt fails compilation.
  Copy the text below into ChatGPT, filling in all three placeholders.
**Purpose**: Feed Lean compiler/checker errors back to the LLM for repair.
**System**: Sys D in benchmark (rounds 1-3).
**Round budget**: Max 3 repair rounds per module. Stop if still failing after round 3.

---

```
You are an expert in both Verilog RTL design and the Lean 4 theorem prover.

The Lean 4 translation below was generated from the Verilog module, but it
contains errors. Your task is to fix all errors and produce a corrected Lean file.

=== ORIGINAL VERILOG ===

{{VERILOG}}

=== PREVIOUS LEAN TRANSLATION (contains errors) ===

{{LEAN_WITH_ERRORS}}

=== COMPILER / CHECKER ERRORS ===

{{ERROR_OUTPUT}}

=== INSTRUCTIONS ===
1. Fix all reported errors.
2. Do NOT introduce `sorry` to suppress errors — fix them properly.
3. Keep the same overall structure (namespace, State/Input/Output structs,
   step/eval functions, theorems). Only change what is necessary to fix errors.
4. If a theorem cannot be proved, DELETE the theorem entirely rather than
   using sorry.
5. Preserve correct parts of the translation unchanged.
6. Make sure all structures still derive `Repr` and `DecidableEq`.

=== OUTPUT ===
Produce only the corrected Lean 4 code. No explanation, no markdown fences,
just the raw Lean source.
```

---

## Logging instructions (for experiment records)

For each module, create a log entry in `logs/<tier>/<module_name>.md`:

```markdown
## <module_name>

- Verilog: <path>
- Prompt used: A_oneshot / A_fewshot / D_repair
- Round 0 (one-shot):
  - Compiles: yes/no
  - sorry-free: yes/no
  - Schema-conformant: yes/no
  - Errors: <paste compiler output if failed>
- Round 1 (repair):
  - Compiles: yes/no
  - sorry-free: yes/no
  - Errors: <paste if failed>
- Round 2 (repair):
  - ...
- Final status: pass / fail-after-3-rounds
- Notes: <observed error categories, e.g. "wrong BitVec width", "missing step case">
```
