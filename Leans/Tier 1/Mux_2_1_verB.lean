namespace Mux_2_1_02

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
  { out :=
      match input.sel with
      | false => input.in0
      | true => input.in1 }

theorem eval_sel_false (in0 in1 : Bit) :
    eval { in0 := in0, in1 := in1, sel := false } = { out := in0 } := rfl

theorem eval_sel_true (in0 in1 : Bit) :
    eval { in0 := in0, in1 := in1, sel := true } = { out := in1 } := rfl

end Mux_2_1_02
