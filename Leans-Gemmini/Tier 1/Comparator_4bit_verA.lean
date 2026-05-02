-- Comparator_4_verA.lean
namespace Comparator_4_verA

abbrev Bit := Bool
abbrev Bits4 := BitVec 4

structure Inputs where
  lhs : Bits4
  rhs : Bits4
deriving Repr, DecidableEq

structure Outputs where
  lt : Bit
  eq : Bit
  gt : Bit
deriving Repr, DecidableEq

def bv4 (n : Nat) : Bits4 := BitVec.ofNat 4 n

def eval (input : Inputs) : Outputs :=
  { lt := decide (input.lhs < input.rhs),
    eq := input.lhs == input.rhs,
    gt := decide (input.lhs > input.rhs) }

theorem test_lt : eval { lhs := bv4 3, rhs := bv4 5 } = { lt := true, eq := false, gt := false } := by native_decide

theorem test_eq : eval { lhs := bv4 4, rhs := bv4 4 } = { lt := false, eq := true, gt := false } := by native_decide

theorem test_gt : eval { lhs := bv4 6, rhs := bv4 2 } = { lt := false, eq := false, gt := true } := by native_decide

end Comparator_4_verA
