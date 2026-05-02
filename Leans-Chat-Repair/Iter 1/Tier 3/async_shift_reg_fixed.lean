import Std

namespace async_shift_register_fifo

abbrev Bit := Bool
abbrev Bits8 := BitVec 8
abbrev Bits5 := BitVec 5

structure State where
  fifo_mem : Array Bits8
  wr_ptr_bin : Bits5
  wr_ptr_gray : Bits5
  rd_ptr_bin : Bits5
  rd_ptr_gray : Bits5
  wr_ptr_gray_sync1 : Bits5
  wr_ptr_gray_sync2 : Bits5
  rd_ptr_gray_sync1 : Bits5
  rd_ptr_gray_sync2 : Bits5
  data_out : Bits8
  deriving Repr, DecidableEq

structure Input where
  rst : Bit
  wr_tick : Bit
  rd_tick : Bit
  write_en : Bit
  read_en : Bit
  data_in : Bits8
  deriving Repr, DecidableEq

structure Output where
  data_out : Bits8
  full : Bit
  empty : Bit
  deriving Repr, DecidableEq

def bv8 (n : Nat) : Bits8 := BitVec.ofNat 8 n

def bv5 (n : Nat) : Bits5 := BitVec.ofNat 5 n

def zeroMem : Array Bits8 := Array.replicate 16 (bv8 0)

def init : State :=
  { fifo_mem := zeroMem
    wr_ptr_bin := bv5 0
    wr_ptr_gray := bv5 0
    rd_ptr_bin := bv5 0
    rd_ptr_gray := bv5 0
    wr_ptr_gray_sync1 := bv5 0
    wr_ptr_gray_sync2 := bv5 0
    rd_ptr_gray_sync1 := bv5 0
    rd_ptr_gray_sync2 := bv5 0
    data_out := bv8 0 }

def gray (x : Bits5) : Bits5 :=
  x ^^^ (x >>> 1)

def invertTopTwo (x : Bits5) : Bits5 :=
  let n := x.toNat
  let low := n % 8
  let b3 := (n / 8) % 2
  let b4 := (n / 16) % 2
  let b3' := if b3 = 0 then 8 else 0
  let b4' := if b4 = 0 then 16 else 0
  bv5 (b4' + b3' + low)

def wrIndex (s : State) : Nat :=
  s.wr_ptr_bin.toNat % 16

def rdIndex (s : State) : Nat :=
  s.rd_ptr_bin.toNat % 16

def fullFlag (s : State) : Bit :=
  gray (s.wr_ptr_bin + bv5 1) == invertTopTwo s.rd_ptr_gray_sync2

def emptyFlag (s : State) : Bit :=
  s.rd_ptr_gray == s.wr_ptr_gray_sync2

def memRead (a : Array Bits8) (idx : Nat) : Bits8 :=
  a.toList.getD idx (bv8 0)

def step (s : State) (i : Input) : State :=
  if i.rst then
    init
  else
    let doWrite := i.wr_tick && i.write_en && !(fullFlag s)
    let doRead := i.rd_tick && i.read_en && !(emptyFlag s)
    let fifo_mem' :=
      if doWrite then
        s.fifo_mem.set! (wrIndex s) i.data_in
      else
        s.fifo_mem
    let wr_ptr_bin' :=
      if doWrite then
        s.wr_ptr_bin + bv5 1
      else
        s.wr_ptr_bin
    let wr_ptr_gray' :=
      if doWrite then
        gray (s.wr_ptr_bin + bv5 1)
      else
        s.wr_ptr_gray
    let rd_ptr_bin' :=
      if doRead then
        s.rd_ptr_bin + bv5 1
      else
        s.rd_ptr_bin
    let rd_ptr_gray' :=
      if doRead then
        gray (s.rd_ptr_bin + bv5 1)
      else
        s.rd_ptr_gray
    let data_out' :=
      if doRead then
        memRead s.fifo_mem (rdIndex s)
      else
        s.data_out
    let rd_ptr_gray_sync1' :=
      if i.wr_tick then s.rd_ptr_gray else s.rd_ptr_gray_sync1
    let rd_ptr_gray_sync2' :=
      if i.wr_tick then s.rd_ptr_gray_sync1 else s.rd_ptr_gray_sync2
    let wr_ptr_gray_sync1' :=
      if i.rd_tick then s.wr_ptr_gray else s.wr_ptr_gray_sync1
    let wr_ptr_gray_sync2' :=
      if i.rd_tick then s.wr_ptr_gray_sync1 else s.wr_ptr_gray_sync2
    { fifo_mem := fifo_mem'
      wr_ptr_bin := wr_ptr_bin'
      wr_ptr_gray := wr_ptr_gray'
      rd_ptr_bin := rd_ptr_bin'
      rd_ptr_gray := rd_ptr_gray'
      wr_ptr_gray_sync1 := wr_ptr_gray_sync1'
      wr_ptr_gray_sync2 := wr_ptr_gray_sync2'
      rd_ptr_gray_sync1 := rd_ptr_gray_sync1'
      rd_ptr_gray_sync2 := rd_ptr_gray_sync2'
      data_out := data_out' }

def out (s : State) : Output :=
  { data_out := s.data_out
    full := fullFlag s
    empty := emptyFlag s }

@[simp] theorem step_reset (s : State) (wrTick rdTick writeEn readEn : Bit) (d : Bits8) :
    step s
      { rst := true
        wr_tick := wrTick
        rd_tick := rdTick
        write_en := writeEn
        read_en := readEn
        data_in := d } = init := by
  simp [step, init]

@[simp] theorem step_hold (s : State) (writeEn readEn : Bit) (d : Bits8) :
    step s
      { rst := false
        wr_tick := false
        rd_tick := false
        write_en := writeEn
        read_en := readEn
        data_in := d } = s := by
  simp [step]

@[simp] theorem out_init :
    out init = { data_out := bv8 0, full := false, empty := true } := by
  native_decide

theorem step_write_from_init :
    step init
      { rst := false
        wr_tick := true
        rd_tick := false
        write_en := true
        read_en := false
        data_in := bv8 42 } =
      { fifo_mem := zeroMem.set! 0 (bv8 42)
        wr_ptr_bin := bv5 1
        wr_ptr_gray := bv5 1
        rd_ptr_bin := bv5 0
        rd_ptr_gray := bv5 0
        wr_ptr_gray_sync1 := bv5 0
        wr_ptr_gray_sync2 := bv5 0
        rd_ptr_gray_sync1 := bv5 0
        rd_ptr_gray_sync2 := bv5 0
        data_out := bv8 0 } := by
  native_decide

theorem step_read_from_visible_entry :
    step
      { fifo_mem := zeroMem.set! 0 (bv8 42)
        wr_ptr_bin := bv5 1
        wr_ptr_gray := bv5 1
        rd_ptr_bin := bv5 0
        rd_ptr_gray := bv5 0
        wr_ptr_gray_sync1 := bv5 1
        wr_ptr_gray_sync2 := bv5 1
        rd_ptr_gray_sync1 := bv5 0
        rd_ptr_gray_sync2 := bv5 0
        data_out := bv8 0 }
      { rst := false
        wr_tick := false
        rd_tick := true
        write_en := false
        read_en := true
        data_in := bv8 0 } =
      { fifo_mem := zeroMem.set! 0 (bv8 42)
        wr_ptr_bin := bv5 1
        wr_ptr_gray := bv5 1
        rd_ptr_bin := bv5 1
        rd_ptr_gray := bv5 1
        wr_ptr_gray_sync1 := bv5 1
        wr_ptr_gray_sync2 := bv5 1
        rd_ptr_gray_sync1 := bv5 0
        rd_ptr_gray_sync2 := bv5 0
        data_out := bv8 42 } := by
  native_decide

theorem step_wr_domain_sync_shift :
    step
      { fifo_mem := zeroMem
        wr_ptr_bin := bv5 0
        wr_ptr_gray := bv5 0
        rd_ptr_bin := bv5 3
        rd_ptr_gray := bv5 2
        wr_ptr_gray_sync1 := bv5 0
        wr_ptr_gray_sync2 := bv5 0
        rd_ptr_gray_sync1 := bv5 5
        rd_ptr_gray_sync2 := bv5 7
        data_out := bv8 0 }
      { rst := false
        wr_tick := true
        rd_tick := false
        write_en := false
        read_en := false
        data_in := bv8 0 } =
      { fifo_mem := zeroMem
        wr_ptr_bin := bv5 0
        wr_ptr_gray := bv5 0
        rd_ptr_bin := bv5 3
        rd_ptr_gray := bv5 2
        wr_ptr_gray_sync1 := bv5 0
        wr_ptr_gray_sync2 := bv5 0
        rd_ptr_gray_sync1 := bv5 2
        rd_ptr_gray_sync2 := bv5 5
        data_out := bv8 0 } := by
  native_decide

end async_shift_register_fifo
