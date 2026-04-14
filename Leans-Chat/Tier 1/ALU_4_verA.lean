import Std

namespace ALU_4_verA_01

abbrev Bit := Bool
abbrev Bits2 := BitVec 2
abbrev Bits4 := BitVec 4

structure Inputs where
lhs : Bits4
rhs : Bits4
op : Bits2
deriving Repr, DecidableEq

structure Outputs where
out : Bits4
deriving Repr, DecidableEq

def bv2 (n : Nat) : Bits2 := BitVec.ofNat 2 n
def bv4 (n : Nat) : Bits4 := BitVec.ofNat 4 n

def eval (input : Inputs) : Outputs :=
if input.op = bv2 0 then
{ out := input.lhs + input.rhs }
else if input.op = bv2 1 then
{ out := input.lhs - input.rhs }
else if input.op = bv2 2 then
{ out := input.lhs &&& input.rhs }
else
{ out := input.lhs ||| input.rhs }

theorem eval_add :
eval { lhs := bv4 3, rhs := bv4 5, op := bv2 0 } = { out := bv4 8 } := by
native_decide

theorem eval_sub :
eval { lhs := bv4 3, rhs := bv4 5, op := bv2 1 } = { out := bv4 14 } := by
native_decide

theorem eval_and :
eval { lhs := bv4 10, rhs := bv4 12, op := bv2 2 } = { out := bv4 8 } := by
native_decide

theorem eval_or :
eval { lhs := bv4 10, rhs := bv4 12, op := bv2 3 } = { out := bv4 14 } := by
native_decide

end ALU_4_verA_01
