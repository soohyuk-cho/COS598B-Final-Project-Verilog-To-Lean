-- Encoder_4_2_verA.lean
namespace Encoder_4_2_verA

abbrev Bits4 := BitVec 4
abbrev Bits2 := BitVec 2

structure Inputs where
  «in» : Bits4
deriving Repr, DecidableEq

structure Outputs where
  out : Bits2
deriving Repr, DecidableEq

def bv4 (n : Nat) : Bits4 := BitVec.ofNat 4 n
def bv2 (n : Nat) : Bits2 := BitVec.ofNat 2 n

def eval (input : Inputs) : Outputs :=
  if input.«in» = bv4 1 then
    { out := bv2 0 }
  else if input.«in» = bv4 2 then
    { out := bv2 1 }
  else if input.«in» = bv4 4 then
    { out := bv2 2 }
  else if input.«in» = bv4 8 then
    { out := bv2 3 }
  else
    { out := bv2 0 }

theorem test_0001 : eval { «in» := bv4 1 } = { out := bv2 0 } := by native_decide

theorem test_0010 : eval { «in» := bv4 2 } = { out := bv2 1 } := by native_decide

theorem test_0100 : eval { «in» := bv4 4 } = { out := bv2 2 } := by native_decide

theorem test_1000 : eval { «in» := bv4 8 } = { out := bv2 3 } := by native_decide

theorem test_default : eval { «in» := bv4 0 } = { out := bv2 0 } := by native_decide

end Encoder_4_2_verA
