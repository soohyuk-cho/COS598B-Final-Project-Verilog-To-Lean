import Std

namespace async_fifo

abbrev Bit := Bool
abbrev Bits8 := BitVec 8
abbrev Bits5 := BitVec 5

structure State where
  mem : Array Bits8
  wr_ptr_bin : Bits5
  wr_ptr_gray : Bits5
  wr_ptr_gray_sync : Bits5
  rd_ptr_bin : Bits5
  rd_ptr_gray : Bits5
  rd_ptr_gray_sync : Bits5
  rd_data : Bits8
  deriving Repr, DecidableEq

structure Input where
  wr_tick : Bit
  rd_tick : Bit
  wr_rst_n : Bit
  rd_rst_n : Bit
  wr_en : Bit
  rd_en : Bit
  wr_data : Bits8
  deriving Repr, DecidableEq

structure Output where
  rd_data : Bits8
  full : Bit
  empty : Bit
  deriving Repr, DecidableEq

def bv8 (n : Nat) : Bits8 := BitVec.ofNat 8 n

def bv5 (n : Nat) : Bits5 := BitVec.ofNat 5 n

def zeroMem : Array Bits8 := Array.mkArray 16 (bv8 0)

def init : State :=
  { mem := zeroMem
    wr_ptr_bin := bv5 0
    wr_ptr_gray := bv5 0
    wr_ptr_gray_sync := bv5 0
    rd_ptr_bin := bv5 0
    rd_ptr_gray := bv5 0
    rd_ptr_gray_sync := bv5 0
    rd_data := bv8 0 }

def grayToBin (g : Bits5) : Bits5 :=
  let b1 : Bits5 := g ^^^ (g >>> 1)
  let b2 : Bits5 := b1 ^^^ (b1 >>> 2)
  let b3 : Bits5 := b2 ^^^ (b2 >>> 4)
  b3

def invertTopBit (x : Bits5) : Bits5 :=
  let lo := x.toNat % 16
  let hi := if ((x.toNat / 16) % 2 = 0) then 16 else 0
  bv5 (hi + lo)

def wrPtrBinSync (s : State) : Bits5 := grayToBin s.wr_ptr_gray_sync

def rdPtrBinSync (s : State) : Bits5 := grayToBin s.rd_ptr_gray_sync

def fullFlag (s : State) : Bit :=
  s.wr_ptr_gray == invertTopBit (rdPtrBinSync s)

def emptyFlag (s : State) : Bit :=
  wrPtrBinSync s == s.rd_ptr_gray

def wrIndex (s : State) : Nat := s.wr_ptr_bin.toNat % 16

def rdIndex (s : State) : Nat := s.rd_ptr_bin.toNat % 16

def nextGray (x : Bits5) : Bits5 :=
  x ^^^ (x >>> 1)

def step (s : State) (i : Input) : State :=
  let wr_ptr_gray_sync' :=
    if i.rd_tick then
      if !i.rd_rst_n then bv5 0 else s.wr_ptr_gray
    else
      s.wr_ptr_gray_sync
  let rd_ptr_gray_sync' :=
    if i.wr_tick then
      if !i.wr_rst_n then bv5 0 else s.rd_ptr_gray
    else
      s.rd_ptr_gray_sync
  let mem' :=
    if i.wr_tick then
      if !i.wr_rst_n then
        s.mem
      else if i.wr_en && !(fullFlag s) then
        s.mem.set! (wrIndex s) i.wr_data
      else
        s.mem
    else
      s.mem
  let wr_ptr_bin' :=
    if i.wr_tick then
      if !i.wr_rst_n then
        bv5 0
      else if i.wr_en && !(fullFlag s) then
        s.wr_ptr_bin + bv5 1
      else
        s.wr_ptr_bin
    else
      s.wr_ptr_bin
  let wr_ptr_gray' :=
    if i.wr_tick then
      if !i.wr_rst_n then
        bv5 0
      else if i.wr_en && !(fullFlag s) then
        nextGray (s.wr_ptr_bin + bv5 1)
      else
        s.wr_ptr_gray
    else
      s.wr_ptr_gray
  let rd_ptr_bin' :=
    if i.rd_tick then
      if !i.rd_rst_n then
        bv5 0
      else if i.rd_en && !(emptyFlag s) then
        s.rd_ptr_bin + bv5 1
      else
        s.rd_ptr_bin
    else
      s.rd_ptr_bin
  let rd_ptr_gray' :=
    if i.rd_tick then
      if !i.rd_rst_n then
        bv5 0
      else if i.rd_en && !(emptyFlag s) then
        nextGray (s.rd_ptr_bin + bv5 1)
      else
        s.rd_ptr_gray
    else
      s.rd_ptr_gray
  let rd_data' :=
    if i.rd_tick then
      if !i.rd_rst_n then
        bv8 0
      else if i.rd_en && !(emptyFlag s) then
        s.mem.get! (rdIndex s)
      else
        s.rd_data
    else
      s.rd_data
  { mem := mem'
    wr_ptr_bin := wr_ptr_bin'
    wr_ptr_gray := wr_ptr_gray'
    wr_ptr_gray_sync := wr_ptr_gray_sync'
    rd_ptr_bin := rd_ptr_bin'
    rd_ptr_gray := rd_ptr_gray'
    rd_ptr_gray_sync := rd_ptr_gray_sync'
    rd_data := rd_data' }

def out (s : State) : Output :=
  { rd_data := s.rd_data
    full := fullFlag s
    empty := emptyFlag s }

@[simp] theorem step_write_reset (s : State) (rdTick rdRstN rdEn : Bit) (d : Bits8) :
    (step s
      { wr_tick := true
        rd_tick := rdTick
        wr_rst_n := false
        rd_rst_n := rdRstN
        wr_en := true
        rd_en := rdEn
        wr_data := d }).wr_ptr_bin = bv5 0 := by
  simp [step]

@[simp] theorem step_read_reset (s : State) (wrTick wrRstN wrEn : Bit) (d : Bits8) :
    (step s
      { wr_tick := wrTick
        rd_tick := true
        wr_rst_n := wrRstN
        rd_rst_n := false
        wr_en := wrEn
        rd_en := true
        wr_data := d }).rd_ptr_bin = bv5 0 := by
  simp [step]

@[simp] theorem step_no_ticks_hold (s : State) (wrRstN rdRstN wrEn rdEn : Bit) (d : Bits8) :
    step s
      { wr_tick := false
        rd_tick := false
        wr_rst_n := wrRstN
        rd_rst_n := rdRstN
        wr_en := wrEn
        rd_en := rdEn
        wr_data := d } = s := by
  simp [step]

theorem init_outputs :
    out init = { rd_data := bv8 0, full := false, empty := true } := by
  native_decide

theorem step_write_from_init :
    step init
      { wr_tick := true
        rd_tick := false
        wr_rst_n := true
        rd_rst_n := true
        wr_en := true
        rd_en := false
        wr_data := bv8 42 } =
      { mem := zeroMem.set! 0 (bv8 42)
        wr_ptr_bin := bv5 1
        wr_ptr_gray := bv5 1
        wr_ptr_gray_sync := bv5 0
        rd_ptr_bin := bv5 0
        rd_ptr_gray := bv5 0
        rd_ptr_gray_sync := bv5 0
        rd_data := bv8 0 } := by
  native_decide

theorem step_read_from_visible_data :
    step
      { mem := zeroMem.set! 0 (bv8 42)
        wr_ptr_bin := bv5 1
        wr_ptr_gray := bv5 1
        wr_ptr_gray_sync := bv5 1
        rd_ptr_bin := bv5 0
        rd_ptr_gray := bv5 0
        rd_ptr_gray_sync := bv5 0
        rd_data := bv8 0 }
      { wr_tick := false
        rd_tick := true
        wr_rst_n := true
        rd_rst_n := true
        wr_en := false
        rd_en := true
        wr_data := bv8 0 } =
      { mem := zeroMem.set! 0 (bv8 42)
        wr_ptr_bin := bv5 1
        wr_ptr_gray := bv5 1
        wr_ptr_gray_sync := bv5 1
        rd_ptr_bin := bv5 1
        rd_ptr_gray := bv5 1
        rd_ptr_gray_sync := bv5 0
        rd_data := bv8 42 } := by
  native_decide

end async_fifo
