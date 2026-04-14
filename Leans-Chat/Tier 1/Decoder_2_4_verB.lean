import Std

namespace Decoder_2_4_verB_01

abbrev Bit := Bool
abbrev Bits2 := BitVec 2
abbrev Bits4 := BitVec 4

structure Inputs where
  «in» : Bits2
deriving Repr, DecidableEq

structure Outputs where
  out : Bits4
deriving Repr, DecidableEq

def bv2 (n : Nat) : Bits2 := BitVec.ofNat 2 n
def bv4 (n : Nat) : Bits4 := BitVec.ofNat 4 n

def eval (input : Inputs) : Outputs :=
  { out := (bv4 1) <<< input.«in».toNat }

theorem eval_in_0 :
    eval { «in» := bv2 0 } = { out := bv4 1 } := by
  native_decide

theorem eval_in_1 :
    eval { «in» := bv2 1 } = { out := bv4 2 } := by
  native_decide

theorem eval_in_2 :
    eval { «in» := bv2 2 } = { out := bv4 4 } := by
  native_decide

theorem eval_in_3 :
    eval { «in» := bv2 3 } = { out := bv4 8 } := by
  native_decide

end Decoder_2_4_verB_01