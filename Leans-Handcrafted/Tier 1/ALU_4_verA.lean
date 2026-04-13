namespace ALU_4_01

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

def bv4 (n : Nat) : Bits4 :=
  BitVec.ofNat 4 n

def bv2 (n : Nat) : Bits2 :=
  BitVec.ofNat 2 n

def eval (input : Inputs) : Outputs :=
  match input.op.toNat with
  | 0 => { out := input.lhs + input.rhs }
  | 1 => { out := input.lhs - input.rhs }
  | 2 => { out := input.lhs &&& input.rhs }
  | _ => { out := input.lhs ||| input.rhs }

theorem eval_add_example :
    eval { lhs := bv4 3, rhs := bv4 5, op := bv2 0 } = { out := bv4 8 } := by
  native_decide

theorem eval_sub_example :
    eval { lhs := bv4 3, rhs := bv4 5, op := bv2 1 } = { out := bv4 14 } := by
  native_decide

theorem eval_and_example :
    eval { lhs := bv4 12, rhs := bv4 10, op := bv2 2 } = { out := bv4 8 } := by
  native_decide

theorem eval_or_example :
    eval { lhs := bv4 12, rhs := bv4 10, op := bv2 3 } = { out := bv4 14 } := by
  native_decide

end ALU_4_01
