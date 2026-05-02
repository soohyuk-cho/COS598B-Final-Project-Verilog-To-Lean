import Std

namespace dual_port_fifo_v2

abbrev Bit := Bool
abbrev Bits8 := BitVec 8
abbrev Bits5 := BitVec 5

structure State where
  fifo_mem : Array Bits8
  wr_ptr : Bits5
  rd_ptr : Bits5
  full : Bit
  rd_data : Bits8
  empty : Bit
deriving Repr, DecidableEq

structure Input where
  rst : Bit
  wr_en : Bit
  wr_data : Bits8
  rd_en : Bit
deriving Repr, DecidableEq

structure Output where
  full : Bit
  rd_data : Bits8
  empty : Bit
deriving Repr, DecidableEq

def bv8 (n : Nat) : Bits8 := BitVec.ofNat 8 n

def bv5 (n : Nat) : Bits5 := BitVec.ofNat 5 n

def zeroMem : Array Bits8 := Array.replicate 16 (bv8 0)

def init : State :=
  { fifo_mem := zeroMem
    wr_ptr := bv5 0
    rd_ptr := bv5 0
    full := false
    rd_data := bv8 0
    empty := true }

def ptrLow (p : Bits5) : Nat :=
  p.toNat % 16

def ptrMsb (p : Bits5) : Nat :=
  p.toNat / 16

def fifo_empty (s : State) : Bool :=
  s.wr_ptr == s.rd_ptr

def fifo_full (s : State) : Bool :=
  (!(ptrMsb s.wr_ptr == ptrMsb s.rd_ptr)) && (ptrLow s.wr_ptr == ptrLow s.rd_ptr)

def memRead (a : Array Bits8) (idx : Nat) : Bits8 :=
  a.toList.getD idx (bv8 0)

def step (s : State) (i : Input) : State :=
  if i.rst then
    { fifo_mem := s.fifo_mem
      wr_ptr := bv5 0
      rd_ptr := bv5 0
      full := false
      rd_data := bv8 0
      empty := true }
  else
    let writeActive := i.wr_en && !s.full
    let readActive := i.rd_en && !s.empty
    let fifo_mem' :=
      if writeActive then
        s.fifo_mem.set! (ptrLow s.wr_ptr) i.wr_data
      else
        s.fifo_mem
    let wr_ptr' :=
      if writeActive then
        s.wr_ptr + bv5 1
      else
        s.wr_ptr
    let rd_ptr' :=
      if readActive then
        s.rd_ptr + bv5 1
      else
        s.rd_ptr
    let rd_data' :=
      if readActive then
        memRead s.fifo_mem (ptrLow s.rd_ptr)
      else
        s.rd_data
    { fifo_mem := fifo_mem'
      wr_ptr := wr_ptr'
      rd_ptr := rd_ptr'
      full := fifo_full s
      rd_data := rd_data'
      empty := fifo_empty s }

def out (s : State) : Output :=
  { full := s.full
    rd_data := s.rd_data
    empty := s.empty }

@[simp] theorem step_reset (s : State) (wrEn rdEn : Bit) (d : Bits8) :
    step s { rst := true, wr_en := wrEn, wr_data := d, rd_en := rdEn } =
      { fifo_mem := s.fifo_mem
        wr_ptr := bv5 0
        rd_ptr := bv5 0
        full := false
        rd_data := bv8 0
        empty := true } := by
  simp [step, bv5, bv8]

@[simp] theorem step_hold (s : State) (d : Bits8) :
    step s { rst := false, wr_en := false, wr_data := d, rd_en := false } =
      { fifo_mem := s.fifo_mem
        wr_ptr := s.wr_ptr
        rd_ptr := s.rd_ptr
        full := fifo_full s
        rd_data := s.rd_data
        empty := fifo_empty s } := by
  simp [step, fifo_full, fifo_empty]

@[simp] theorem step_write_only_mem (s : State) (d : Bits8) (h : s.full = false) :
    (step s { rst := false, wr_en := true, wr_data := d, rd_en := false }).fifo_mem =
      s.fifo_mem.set! (ptrLow s.wr_ptr) d := by
  simp [step, fifo_full, fifo_empty, h]

@[simp] theorem step_write_only_wr_ptr (s : State) (d : Bits8) (h : s.full = false) :
    (step s { rst := false, wr_en := true, wr_data := d, rd_en := false }).wr_ptr =
      s.wr_ptr + bv5 1 := by
  simp [step, fifo_full, fifo_empty, h]

@[simp] theorem step_read_only_rd_ptr (s : State) (d : Bits8) (h : s.empty = false) :
    (step s { rst := false, wr_en := false, wr_data := d, rd_en := true }).rd_ptr =
      s.rd_ptr + bv5 1 := by
  simp [step, fifo_full, fifo_empty, h]

@[simp] theorem step_read_only_rd_data (s : State) (d : Bits8) (h : s.empty = false) :
    (step s { rst := false, wr_en := false, wr_data := d, rd_en := true }).rd_data =
      memRead s.fifo_mem (ptrLow s.rd_ptr) := by
  simp [step, fifo_full, fifo_empty, h, memRead]

@[simp] theorem step_simultaneous_ptrs (s : State) (d : Bits8)
    (hfull : s.full = false) (hempty : s.empty = false) :
    (step s { rst := false, wr_en := true, wr_data := d, rd_en := true }).wr_ptr = s.wr_ptr + bv5 1
    ∧ (step s { rst := false, wr_en := true, wr_data := d, rd_en := true }).rd_ptr = s.rd_ptr + bv5 1 := by
  simp [step, fifo_full, fifo_empty, hfull, hempty]

@[simp] theorem out_def (s : State) :
    out s = { full := s.full, rd_data := s.rd_data, empty := s.empty } := rfl

theorem init_out :
    out init = { full := false, rd_data := bv8 0, empty := true } := by
  native_decide

theorem step_write_from_init :
    step init { rst := false, wr_en := true, wr_data := bv8 42, rd_en := false } =
      { fifo_mem := zeroMem.set! 0 (bv8 42)
        wr_ptr := bv5 1
        rd_ptr := bv5 0
        full := false
        rd_data := bv8 0
        empty := true } := by
  native_decide

theorem step_idle_after_first_write :
    step
      { fifo_mem := zeroMem.set! 0 (bv8 42)
        wr_ptr := bv5 1
        rd_ptr := bv5 0
        full := false
        rd_data := bv8 0
        empty := true }
      { rst := false, wr_en := false, wr_data := bv8 0, rd_en := false } =
      { fifo_mem := zeroMem.set! 0 (bv8 42)
        wr_ptr := bv5 1
        rd_ptr := bv5 0
        full := false
        rd_data := bv8 0
        empty := false } := by
  native_decide

end dual_port_fifo_v2
