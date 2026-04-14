import Std

namespace ALU_4_verB_01

abbrev Bit := Bool
abbrev Bits4 := BitVec 4
abbrev Bits2 := BitVec 2

structure Inputs where
lhs : Bits4
rhs : Bits4
op : Bits2
deriving Repr, DecidableEq

structure Outputs where
out : Bits4
deriving Repr, DecidableEq

def bv4 (n : Nat) : Bits4 := BitVec.ofNat 4 n
def bv2 (n : Nat) : Bits2 := BitVec.ofNat 2 n

def eval (input : Inputs) : Outputs :=
let add_result : Bits4 := input.lhs + input.rhs
let sub_result : Bits4 := input.lhs - input.rhs
let and_result : Bits4 := input.lhs &&& input.rhs
let or_result : Bits4 := input.lhs ||| input.rhs
{ out :=
if input.op = bv2 0 then
add_result
else if input.op = bv2 1 then
sub_result
else if input.op = bv2 2 then
and_result
else
or_result }

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

end ALU_4_verB_01
