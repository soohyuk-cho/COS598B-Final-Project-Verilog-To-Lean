import Std

namespace Comparator_4_verA_01

abbrev Bit := Bool

structure Inputs where
lhs : BitVec 4
rhs : BitVec 4
deriving Repr, DecidableEq

structure Outputs where
lt : Bit
eq : Bit
gt : Bit
deriving Repr, DecidableEq

def eval (input : Inputs) : Outputs :=
{ lt := decide (input.lhs.toNat < input.rhs.toNat)
  eq := decide (input.lhs = input.rhs)
  gt := decide (input.lhs.toNat > input.rhs.toNat) }

@[simp] theorem eval_equal (x : BitVec 4) :
eval { lhs := x, rhs := x } = { lt := false, eq := true, gt := false } := by
simp [eval]

@[simp] theorem eval_lt_true (lhs rhs : BitVec 4) (h : lhs.toNat < rhs.toNat) :
(eval { lhs := lhs, rhs := rhs }).lt = true := by
simp [eval, h]

@[simp] theorem eval_gt_true (lhs rhs : BitVec 4) (h : lhs.toNat > rhs.toNat) :
(eval { lhs := lhs, rhs := rhs }).gt = true := by
simp [eval, h]

end Comparator_4_verA_01
