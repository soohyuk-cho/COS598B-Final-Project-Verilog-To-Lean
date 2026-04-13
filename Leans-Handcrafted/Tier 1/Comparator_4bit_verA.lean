namespace Comparator_4bit_01

abbrev Bits4 := BitVec 4
abbrev Bit := Bool

structure Inputs where
  lhs : Bits4
  rhs : Bits4
deriving Repr, DecidableEq

structure Outputs where
  lt : Bit
  eq : Bit
  gt : Bit
deriving Repr, DecidableEq

def bv4 (n : Nat) : Bits4 :=
  BitVec.ofNat 4 n

def eval (input : Inputs) : Outputs :=
  { lt := input.lhs < input.rhs
  , eq := input.lhs = input.rhs
  , gt := input.lhs > input.rhs }

theorem eval_lt_example :
    eval { lhs := bv4 3, rhs := bv4 5 } =
      { lt := true, eq := false, gt := false } := by
  native_decide

theorem eval_eq_example :
    eval { lhs := bv4 6, rhs := bv4 6 } =
      { lt := false, eq := true, gt := false } := by
  native_decide

theorem eval_gt_example :
    eval { lhs := bv4 12, rhs := bv4 2 } =
      { lt := false, eq := false, gt := true } := by
  native_decide

end Comparator_4bit_01
