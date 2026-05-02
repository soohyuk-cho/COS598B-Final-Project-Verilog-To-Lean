import Std

namespace circular_buffer

abbrev Bit := Bool
abbrev Bits8 := BitVec 8
abbrev Bits4 := BitVec 4

structure State where
  mem : Array Bits8
  rd_ptr : Bits4
  wr_ptr : Bits4
  rd_data : Bits8
  full_flag : Bit
  empty_flag : Bit
deriving Repr, DecidableEq

structure Input where
  reset : Bit
  wr_en : Bit
  wr_data : Bits8
  rd_en : Bit
deriving Repr, DecidableEq

structure Output where
  rd_data : Bits8
  full : Bit
  empty : Bit
deriving Repr, DecidableEq

def bv8 (n : Nat) : Bits8 := BitVec.ofNat 8 n

def bv4 (n : Nat) : Bits4 := BitVec.ofNat 4 n

def zeroMem : Array Bits8 := Array.replicate 16 (bv8 0)

def init : State :=
  { mem := zeroMem
    rd_ptr := bv4 0
    wr_ptr := bv4 0
    rd_data := bv8 0
    full_flag := false
    empty_flag := true }

def idx (p : Bits4) : Nat :=
  p.toNat

def memRead (a : Array Bits8) (i : Nat) : Bits8 :=
  a.toList.getD i (bv8 0)

def step (s : State) (i : Input) : State :=
  if i.reset then
    init
  else
    let rd_ptr_next := s.rd_ptr + bv4 1
    let wr_ptr_next := s.wr_ptr + bv4 1
    let write_active := i.wr_en && !s.full_flag
    let read_active := i.rd_en && !s.empty_flag
    let mem' :=
      if write_active then
        s.mem.set! (idx s.wr_ptr) i.wr_data
      else
        s.mem
    let wr_ptr' :=
      if write_active then
        wr_ptr_next
      else
        s.wr_ptr
    let rd_ptr' :=
      if read_active then
        rd_ptr_next
      else
        s.rd_ptr
    let rd_data' :=
      if read_active then
        memRead s.mem (idx s.rd_ptr)
      else
        s.rd_data
    let full_after_write :=
      if write_active then
        if wr_ptr_next == s.rd_ptr then true else s.full_flag
      else
        s.full_flag
    let empty_after_write :=
      if write_active then false else s.empty_flag
    let full' :=
      if read_active then false else full_after_write
    let empty' :=
      if read_active then
        if s.wr_ptr == rd_ptr_next then true else empty_after_write
      else
        empty_after_write
    { mem := mem'
      rd_ptr := rd_ptr'
      wr_ptr := wr_ptr'
      rd_data := rd_data'
      full_flag := full'
      empty_flag := empty' }

def out (s : State) : Output :=
  { rd_data := s.rd_data
    full := s.full_flag
    empty := s.empty_flag }

@[simp] theorem step_reset (s : State) (wrEn rdEn : Bit) (d : Bits8) :
    step s { reset := true, wr_en := wrEn, wr_data := d, rd_en := rdEn } = init := by
  simp [step, init]

@[simp] theorem step_hold (s : State) (d : Bits8) :
    step s { reset := false, wr_en := false, wr_data := d, rd_en := false } = s := by
  simp [step, idx, memRead]

@[simp] theorem step_write_only_wr_ptr (s : State) (d : Bits8) (h : s.full_flag = false) :
    (step s { reset := false, wr_en := true, wr_data := d, rd_en := false }).wr_ptr = s.wr_ptr + bv4 1 := by
  simp [step, idx, memRead, h]

@[simp] theorem step_write_only_mem (s : State) (d : Bits8) (h : s.full_flag = false) :
    (step s { reset := false, wr_en := true, wr_data := d, rd_en := false }).mem =
      s.mem.set! (idx s.wr_ptr) d := by
  simp [step, idx, memRead, h]

@[simp] theorem step_read_only_rd_ptr (s : State) (d : Bits8) (h : s.empty_flag = false) :
    (step s { reset := false, wr_en := false, wr_data := d, rd_en := true }).rd_ptr = s.rd_ptr + bv4 1 := by
  simp [step, idx, memRead, h]

@[simp] theorem step_read_only_rd_data (s : State) (d : Bits8) (h : s.empty_flag = false) :
    (step s { reset := false, wr_en := false, wr_data := d, rd_en := true }).rd_data =
      memRead s.mem (idx s.rd_ptr) := by
  simp [step, idx, memRead, h]

@[simp] theorem out_def (s : State) :
    out s = { rd_data := s.rd_data, full := s.full_flag, empty := s.empty_flag } := rfl

theorem init_out :
    out init = { rd_data := bv8 0, full := false, empty := true } := by
  native_decide

theorem step_write_from_init :
    step init { reset := false, wr_en := true, wr_data := bv8 37, rd_en := false } =
      { mem := zeroMem.set! 0 (bv8 37)
        rd_ptr := bv4 0
        wr_ptr := bv4 1
        rd_data := bv8 0
        full_flag := false
        empty_flag := false } := by
  native_decide

theorem step_read_from_one_element :
    step
      { mem := zeroMem.set! 0 (bv8 37)
        rd_ptr := bv4 0
        wr_ptr := bv4 1
        rd_data := bv8 0
        full_flag := false
        empty_flag := false }
      { reset := false, wr_en := false, wr_data := bv8 0, rd_en := true } =
      { mem := zeroMem.set! 0 (bv8 37)
        rd_ptr := bv4 1
        wr_ptr := bv4 1
        rd_data := bv8 37
        full_flag := false
        empty_flag := true } := by
  native_decide

end circular_buffer
