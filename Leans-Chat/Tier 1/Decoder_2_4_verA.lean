import Std

namespace Decoder_2_4_verA_01

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
if input.«in» = bv2 0 then
{ out := bv4 1 }
else if input.«in» = bv2 1 then
{ out := bv4 2 }
else if input.«in» = bv2 2 then
{ out := bv4 4 }
else
{ out := bv4 8 }

theorem case_00 : eval { «in» := bv2 0 } = { out := bv4 1 } := by native_decide

theorem case_01 : eval { «in» := bv2 1 } = { out := bv4 2 } := by native_decide

theorem case_10 : eval { «in» := bv2 2 } = { out := bv4 4 } := by native_decide

theorem case_11 : eval { «in» := bv2 3 } = { out := bv4 8 } := by native_decide

end Decoder_2_4_verA_01