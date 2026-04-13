import Std

namespace threshold_fifo

abbrev Bit := Bool
abbrev Bits4 := BitVec 4
abbrev Bits5 := BitVec 5
abbrev Bits8 := BitVec 8

structure State where
  fifo_mem : Array Bits8
  write_ptr : Bits4
  read_ptr : Bits4
  fifo_count : Bits5
  read_data : Bits8
  deriving Repr, DecidableEq

structure Input where
  reset : Bit
  write_enable : Bit
  read_enable : Bit
  write_data : Bits8
  deriving Repr, DecidableEq

structure Output where
  read_data : Bits8
  fifo_full : Bit
  fifo_empty : Bit
  high_threshold_reached : Bit
  low_threshold_reached : Bit
  deriving Repr, DecidableEq

def bv4 (n : Nat) : Bits4 := BitVec.ofNat 4 n

def bv5 (n : Nat) : Bits5 := BitVec.ofNat 5 n

def bv8 (n : Nat) : Bits8 := BitVec.ofNat 8 n

def init : State :=
  { fifo_mem := Array.replicate 16 (bv8 0)
    write_ptr := bv4 0
    read_ptr := bv4 0
    fifo_count := bv5 0
    read_data := bv8 0 }


def fifoFull (s : State) : Bit :=
  s.fifo_count.toNat = 16


def fifoEmpty (s : State) : Bit :=
  s.fifo_count.toNat = 0


def highThresholdReached (s : State) : Bit :=
  s.fifo_count.toNat >= 12


def lowThresholdReached (s : State) : Bit :=
  s.fifo_count.toNat <= 3


def step (s : State) (i : Input) : State :=
  if i.reset then
    init
  else
    let doWrite := i.write_enable && !(fifoFull s)
    let doRead := i.read_enable && !(fifoEmpty s)
    let mem' := if doWrite then s.fifo_mem.set! (s.write_ptr.toNat) i.write_data else s.fifo_mem
    let write_ptr' := if doWrite then s.write_ptr + bv4 1 else s.write_ptr
    let read_ptr' := if doRead then s.read_ptr + bv4 1 else s.read_ptr
    let fifo_count' :=
      if doRead then s.fifo_count - bv5 1
      else if doWrite then s.fifo_count + bv5 1
      else s.fifo_count
    let read_data' := if doRead then s.fifo_mem.get! (s.read_ptr.toNat) else s.read_data
    { fifo_mem := mem'
      write_ptr := write_ptr'
      read_ptr := read_ptr'
      fifo_count := fifo_count'
      read_data := read_data' }


def out (s : State) : Output :=
  { read_data := s.read_data
    fifo_full := fifoFull s
    fifo_empty := fifoEmpty s
    high_threshold_reached := highThresholdReached s
    low_threshold_reached := lowThresholdReached s }

@[simp] theorem step_reset (s : State) (we re : Bit) (wd : Bits8) :
    step s { reset := true, write_enable := we, read_enable := re, write_data := wd } = init := by
  simp [step, init]

@[simp] theorem step_hold (s : State) (wd : Bits8) :
    step s { reset := false, write_enable := false, read_enable := false, write_data := wd } = s := by
  simp [step, fifoFull, fifoEmpty]

@[simp] theorem step_write_only (s : State) (wd : Bits8) (hfull : fifoFull s = false) :
    step s { reset := false, write_enable := true, read_enable := false, write_data := wd } =
      { fifo_mem := s.fifo_mem.set! (s.write_ptr.toNat) wd
        write_ptr := s.write_ptr + bv4 1
        read_ptr := s.read_ptr
        fifo_count := s.fifo_count + bv5 1
        read_data := s.read_data } := by
  simp [step, hfull, fifoFull, fifoEmpty]

@[simp] theorem step_read_only (s : State) (wd : Bits8) (hempty : fifoEmpty s = false) :
    step s { reset := false, write_enable := false, read_enable := true, write_data := wd } =
      { fifo_mem := s.fifo_mem
        write_ptr := s.write_ptr
        read_ptr := s.read_ptr + bv4 1
        fifo_count := s.fifo_count - bv5 1
        read_data := s.fifo_mem.get! (s.read_ptr.toNat) } := by
  simp [step, hempty, fifoFull, fifoEmpty]

@[simp] theorem step_write_read (s : State) (wd : Bits8)
    (hfull : fifoFull s = false) (hempty : fifoEmpty s = false) :
    step s { reset := false, write_enable := true, read_enable := true, write_data := wd } =
      { fifo_mem := s.fifo_mem.set! (s.write_ptr.toNat) wd
        write_ptr := s.write_ptr + bv4 1
        read_ptr := s.read_ptr + bv4 1
        fifo_count := s.fifo_count - bv5 1
        read_data := s.fifo_mem.get! (s.read_ptr.toNat) } := by
  simp [step, hfull, hempty, fifoFull, fifoEmpty]

@[simp] theorem out_eq (s : State) :
    out s =
      { read_data := s.read_data
        fifo_full := fifoFull s
        fifo_empty := fifoEmpty s
        high_threshold_reached := highThresholdReached s
        low_threshold_reached := lowThresholdReached s } := rfl

end threshold_fifo
