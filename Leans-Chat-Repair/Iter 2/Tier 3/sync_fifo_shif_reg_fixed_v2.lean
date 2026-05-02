import Std

namespace synchronous_shift_register_fifo

abbrev Bit := Bool
abbrev Bits8 := BitVec 8
abbrev CountBits := BitVec 3

def DEPTH : Nat := 4

def bv8 (n : Nat) : Bits8 := BitVec.ofNat 8 n

def bv3 (n : Nat) : CountBits := BitVec.ofNat 3 n

structure State where
  shift_reg : Array Bits8
  count : CountBits
  data_out : Bits8
  deriving Repr, DecidableEq

structure Input where
  write_en : Bit
  read_en : Bit
  data_in : Bits8
  deriving Repr, DecidableEq

structure Output where
  data_out : Bits8
  full : Bit
  empty : Bit
  deriving Repr, DecidableEq

def init : State :=
  { shift_reg := Array.replicate DEPTH (bv8 0)
    count := bv3 0
    data_out := bv8 0 }

def full (s : State) : Bit :=
  s.count = bv3 DEPTH

def empty (s : State) : Bit :=
  s.count = bv3 0

def readValue (s : State) : Bits8 :=
  match s.count.toNat with
  | 0 => bv8 0
  | 1 => s.shift_reg.getD 0 (bv8 0)
  | 2 => s.shift_reg.getD 1 (bv8 0)
  | 3 => s.shift_reg.getD 2 (bv8 0)
  | _ => s.shift_reg.getD 3 (bv8 0)

def shiftForWrite (buf : Array Bits8) (count : CountBits) (d : Bits8) : Array Bits8 :=
  match count.toNat with
  | 0 =>
      buf.set! 0 d
  | 1 =>
      let x0 := buf.getD 0 (bv8 0)
      (buf.set! 1 x0).set! 0 d
  | 2 =>
      let x0 := buf.getD 0 (bv8 0)
      let x1 := buf.getD 1 (bv8 0)
      ((buf.set! 2 x1).set! 1 x0).set! 0 d
  | _ =>
      let x0 := buf.getD 0 (bv8 0)
      let x1 := buf.getD 1 (bv8 0)
      let x2 := buf.getD 2 (bv8 0)
      (((buf.set! 3 x2).set! 2 x1).set! 1 x0).set! 0 d

def step (rst : Bit) (s : State) (i : Input) : State :=
  if rst then
    init
  else
    let doRead : Bit := i.read_en && !(empty s)
    let doWrite : Bit := i.write_en && !(full s)
    let nextDataOut := if doRead then readValue s else s.data_out
    let nextShiftReg := if doWrite then shiftForWrite s.shift_reg s.count i.data_in else s.shift_reg
    let nextCount :=
      if doWrite && !doRead then
        s.count + bv3 1
      else if doRead && !doWrite then
        s.count - bv3 1
      else
        s.count
    { shift_reg := nextShiftReg
      count := nextCount
      data_out := nextDataOut }

def out (s : State) : Output :=
  { data_out := s.data_out
    full := full s
    empty := empty s }

@[simp] theorem step_reset (s : State) (i : Input) :
    step true s i = init := by
  simp [step, init]

@[simp] theorem step_hold (s : State) (d : Bits8) :
    step false s { write_en := false, read_en := false, data_in := d } = s := by
  simp [step, empty, full]

@[simp] theorem out_init :
    out init = { data_out := bv8 0, full := false, empty := true } := by
  native_decide

end synchronous_shift_register_fifo
