-- Mux_2_1_verB.lean
namespace Mux_2_1_verB

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
  if input.sel = false then
    { out := input.in0 }
  else
    { out := input.in1 }

theorem test_sel_0 : eval { in0 := true, in1 := false, sel := false } = { out := true } := by native_decide

theorem test_sel_1 : eval { in0 := false, in1 := true, sel := true } = { out := true } := by native_decide

end Mux_2_1_verB
