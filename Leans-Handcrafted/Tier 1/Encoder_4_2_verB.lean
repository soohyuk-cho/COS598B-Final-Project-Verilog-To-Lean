namespace Encoder_4_2_02

abbrev Bits4 := BitVec 4
abbrev Bits2 := BitVec 2

structure Inputs where
  «in» : Bits4
deriving Repr, DecidableEq

structure Outputs where
  «out» : Bits2
deriving Repr, DecidableEq

def bv4 (n : Nat) : Bits4 :=
  BitVec.ofNat 4 n

def bv2 (n : Nat) : Bits2 :=
  BitVec.ofNat 2 n

def eval (input : Inputs) : Outputs :=
  let msb := input.«in».getLsbD 2 || input.«in».getLsbD 3
  let lsb := input.«in».getLsbD 1 || input.«in».getLsbD 3
  { «out» := (BitVec.ofBool msb) ++ (BitVec.ofBool lsb) }

theorem eval_in0 :
    eval { «in» := bv4 1 } = { «out» := bv2 0 } := by
  native_decide

theorem eval_in1 :
    eval { «in» := bv4 2 } = { «out» := bv2 1 } := by
  native_decide

theorem eval_in2 :
    eval { «in» := bv4 4 } = { «out» := bv2 2 } := by
  native_decide

theorem eval_in3 :
    eval { «in» := bv4 8 } = { «out» := bv2 3 } := by
  native_decide

end Encoder_4_2_02
