import Std

namespace Mux_2_1_verA_01

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

theorem eval_sel_false : eval { in0 := true, in1 := false, sel := false } = { out := true } := by
  native_decide

theorem eval_sel_true : eval { in0 := false, in1 := true, sel := true } = { out := true } := by
  native_decide

end Mux_2_1_verA_01
