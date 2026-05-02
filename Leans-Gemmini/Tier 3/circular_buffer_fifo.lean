import Std

namespace circular_buffer

structure State (d a size : Nat) where
  mem        : List (BitVec d)
  rd_data    : BitVec d
  rd_ptr     : BitVec a
  wr_ptr     : BitVec a
  full_flag  : Bool
  empty_flag : Bool
deriving Repr, DecidableEq

structure Input (d : Nat) where
  reset   : Bool
  wr_en   : Bool
  rd_en   : Bool
  wr_data : BitVec d
deriving Repr, DecidableEq

structure Output (d : Nat) where
  rd_data : BitVec d
  full    : Bool
  empty   : Bool
deriving Repr, DecidableEq

def init {d a size : Nat} : State d a size :=
  { mem        := List.replicate size (BitVec.ofNat d 0)
  , rd_data    := BitVec.ofNat d 0
  , rd_ptr     := BitVec.ofNat a 0
  , wr_ptr     := BitVec.ofNat a 0
  , full_flag  := false
  , empty_flag := true }

def step {d a size : Nat} (s : State d a size) (i : Input d) : State d a size :=
  if i.reset then
    init
  else
    let we := i.wr_en && !s.full_flag
    let re := i.rd_en && !s.empty_flag
    let wr_ptr_next := s.wr_ptr + 1
    let rd_ptr_next := s.rd_ptr + 1

    let next_mem := if we then s.mem.set (s.wr_ptr.toNat % size) i.wr_data else s.mem
    let next_wr_ptr := if we then wr_ptr_next else s.wr_ptr

    let next_rd_data := if re then s.mem.getD (s.rd_ptr.toNat % size) (BitVec.ofNat d 0) else s.rd_data
    let next_rd_ptr := if re then rd_ptr_next else s.rd_ptr

    let next_full_flag :=
      if re then false
      else if we then (if wr_ptr_next == s.rd_ptr then true else s.full_flag)
      else s.full_flag

    let next_empty_flag :=
      if we then false
      else if re then (if s.wr_ptr == rd_ptr_next then true else s.empty_flag)
      else s.empty_flag

    { mem        := next_mem
    , rd_data    := next_rd_data
    , rd_ptr     := next_rd_ptr
    , wr_ptr     := next_wr_ptr
    , full_flag  := next_full_flag
    , empty_flag := next_empty_flag }

def out {d a size : Nat} (s : State d a size) : Output d :=
  { rd_data := s.rd_data
  , full    := s.full_flag
  , empty   := s.empty_flag }

@[simp] theorem step_reset {d a size : Nat} (s : State d a size) (we re : Bool) (wd : BitVec d) :
  step s { reset := true, wr_en := we, rd_en := re, wr_data := wd } = init := by
  simp [step, init]

@[simp] theorem step_hold {d a size : Nat} (s : State d a size) (wd : BitVec d) :
  step s { reset := false, wr_en := false, rd_en := false, wr_data := wd } = s := by
  simp [step]

end circular_buffer
