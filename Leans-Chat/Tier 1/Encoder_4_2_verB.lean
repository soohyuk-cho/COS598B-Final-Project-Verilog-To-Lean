
import Std

namespace Encoder_4_2_verB_01

abbrev Bit := Bool
abbrev Bits2 := BitVec 2
abbrev Bits4 := BitVec 4

structure Inputs where
«in» : Bits4
deriving Repr, DecidableEq

structure Outputs where
out : Bits2
deriving Repr, DecidableEq

def bv2 (n : Nat) : Bits2 := BitVec.ofNat 2 n
def bv4 (n : Nat) : Bits4 := BitVec.ofNat 4 n

def bitVal (b : Bool) : Nat := if b then 1 else 0

def eval (input : Inputs) : Outputs :=
let b1 := input.«in».getLsb 1
let b2 := input.«in».getLsb 2
let b3 := input.«in».getLsb 3
{ out := bv2 (bitVal (b1 || b3) + 2 * bitVal (b2 || b3)) }

theorem eval_zero :
eval { «in» := bv4 0 } = { out := bv2 0 } := by
native_decide

theorem eval_in1 :
eval { «in» := bv4 2 } = { out := bv2 1 } := by
native_decide

theorem eval_in2 :
eval { «in» := bv4 4 } = { out := bv2 2 } := by
native_decide

theorem eval_in3 :
eval { «in» := bv4 8 } = { out := bv2 3 } := by
native_decide

end Encoder_4_2_verB_01
