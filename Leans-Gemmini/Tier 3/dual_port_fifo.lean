import Std

namespace dual_port_fifo_v2

structure State (d a : Nat) where
  mem     : List (BitVec d)
  wr_ptr  : BitVec (a + 1)
  rd_ptr  : BitVec (a + 1)
  rd_data : BitVec d
  full    : Bool
  empty   : Bool
deriving Repr, DecidableEq

structure Input (d : Nat) where
  rst     : Bool
  wr_en   : Bool
  rd_en   : Bool
  wr_data : BitVec d
deriving Repr, DecidableEq

structure Output (d : Nat) where
  rd_data : BitVec d
  full    : Bool
  empty   : Bool
deriving Repr, DecidableEq

def init {d a : Nat} : State d a :=
  { mem     := List.replicate (2 ^ a) (BitVec.ofNat d 0)
  , wr_ptr  := BitVec.ofNat (a + 1) 0
  , rd_ptr  := BitVec.ofNat (a + 1) 0
  , rd_data := BitVec.ofNat d 0
  , full    := false
  , empty   := true }

def step {d a : Nat} (s : State d a) (i : Input d) : State d a :=
  if i.rst then
    init
  else
    let fifo_empty := s.wr_ptr == s.rd_ptr
    let fifo_full  := s.wr_ptr == (s.rd_ptr ^^^ BitVec.ofNat (a + 1) (1 <<< a))

    let we := i.wr_en && !s.full
    let mask := BitVec.ofNat (a + 1) ((1 <<< a) - 1)
    let wr_idx := (s.wr_ptr &&& mask).toNat
    let next_mem := if we then s.mem.set wr_idx i.wr_data else s.mem
    let next_wr_ptr := if we then s.wr_ptr + 1 else s.wr_ptr

    let re := i.rd_en && !s.empty
    let rd_idx := (s.rd_ptr &&& mask).toNat
    let next_rd_data := if re then s.mem.getD rd_idx (BitVec.ofNat d 0) else s.rd_data
    let next_rd_ptr := if re then s.rd_ptr + 1 else s.rd_ptr

    { mem     := next_mem
    , wr_ptr  := next_wr_ptr
    , rd_ptr  := next_rd_ptr
    , rd_data := next_rd_data
    , full    := fifo_full
    , empty   := fifo_empty }

def out {d a : Nat} (s : State d a) : Output d :=
  { rd_data := s.rd_data
  , full    := s.full
  , empty   := s.empty }

@[simp] theorem step_reset {d a : Nat} (s : State d a) (we re : Bool) (wd : BitVec d) :
  step s { rst := true, wr_en := we, rd_en := re, wr_data := wd } = init := by
  simp [step, init]

@[simp] theorem step_hold {d a : Nat} (s : State d a) (wd : BitVec d) :
  step s { rst := false, wr_en := false, rd_en := false, wr_data := wd } =
  { s with
    full  := s.wr_ptr == (s.rd_ptr ^^^ BitVec.ofNat (a + 1) (1 <<< a)),
    empty := s.wr_ptr == s.rd_ptr } := by
  simp [step]

end dual_port_fifo_v2
