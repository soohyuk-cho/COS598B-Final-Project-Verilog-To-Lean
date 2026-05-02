import Std

namespace synchronous_shift_register_fifo

structure State (w d : Nat) where
  shift_reg : List (BitVec w)
  count     : Nat
  data_out  : BitVec w
deriving Repr, DecidableEq

structure Input (w : Nat) where
  rst      : Bool
  write_en : Bool
  read_en  : Bool
  data_in  : BitVec w
deriving Repr, DecidableEq

structure Output (w : Nat) where
  data_out : BitVec w
  full     : Bool
  empty    : Bool
deriving Repr, DecidableEq

def init {w d : Nat} : State w d :=
  { shift_reg := List.replicate d (BitVec.ofNat w 0)
  , count     := 0
  , data_out  := BitVec.ofNat w 0 }

def listGetD {α} (l : List α) (idx : Nat) (default : α) : α :=
  match l.drop idx with
  | [] => default
  | x :: _ => x

def shift_insert {w : Nat} (reg : List (BitVec w)) (count : Nat) (data_in : BitVec w) : List (BitVec w) :=
  (data_in :: reg.take count) ++ reg.drop (count + 1)

def step {w d : Nat} (s : State w d) (i : Input w) : State w d :=
  if i.rst then
    init
  else
    let full  := s.count == d
    let empty := s.count == 0
    let we    := i.write_en && !full
    let re    := i.read_en && !empty

    let next_data_out := if re then listGetD s.shift_reg (s.count - 1) (BitVec.ofNat w 0) else s.data_out
    let next_shift_reg := if we then shift_insert s.shift_reg s.count i.data_in else s.shift_reg
    let next_count :=
      if we && !re then s.count + 1
      else if !we && re then s.count - 1
      else s.count

    { shift_reg := next_shift_reg
    , count     := next_count
    , data_out  := next_data_out }

def out {w d : Nat} (s : State w d) : Output w :=
  let full  := s.count == d
  let empty := s.count == 0
  { data_out := s.data_out
  , full     := full
  , empty    := empty }

@[simp] theorem step_reset {w d : Nat} (s : State w d) (we re : Bool) (din : BitVec w) :
  step s { rst := true, write_en := we, read_en := re, data_in := din } = init := by
  simp [step, init]

@[simp] theorem step_hold {w d : Nat} (s : State w d) (din : BitVec w) :
  step s { rst := false, write_en := false, read_en := false, data_in := din } = s := by
  simp [step]

end synchronous_shift_register_fifo
