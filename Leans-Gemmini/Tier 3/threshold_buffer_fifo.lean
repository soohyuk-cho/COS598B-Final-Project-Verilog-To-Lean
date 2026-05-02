import Std

namespace threshold_fifo

structure State (d a depth : Nat) where
  mem        : List (BitVec d)
  write_ptr  : BitVec a
  read_ptr   : BitVec a
  fifo_count : BitVec (a + 1)
  read_data  : BitVec d
deriving Repr, DecidableEq

structure Input (d : Nat) where
  reset        : Bool
  write_enable : Bool
  read_enable  : Bool
  write_data   : BitVec d
deriving Repr, DecidableEq

structure Output (d : Nat) where
  read_data              : BitVec d
  fifo_full              : Bool
  fifo_empty             : Bool
  high_threshold_reached : Bool
  low_threshold_reached  : Bool
deriving Repr, DecidableEq

def init {d a depth : Nat} : State d a depth :=
  { mem        := List.replicate depth (BitVec.ofNat d 0)
  , write_ptr  := BitVec.ofNat a 0
  , read_ptr   := BitVec.ofNat a 0
  , fifo_count := BitVec.ofNat (a + 1) 0
  , read_data  := BitVec.ofNat d 0 }

def step {d a depth : Nat} (s : State d a depth) (i : Input d) : State d a depth :=
  if i.reset then
    init
  else
    let fifo_full := s.fifo_count == BitVec.ofNat (a + 1) depth
    let fifo_empty := s.fifo_count == BitVec.ofNat (a + 1) 0
    let we := i.write_enable && !fifo_full
    let re := i.read_enable && !fifo_empty

    let next_mem := if we then s.mem.set (s.write_ptr.toNat % depth) i.write_data else s.mem
    let next_write_ptr := if we then s.write_ptr + 1 else s.write_ptr

    let next_read_data := if re then s.mem.getD (s.read_ptr.toNat % depth) (BitVec.ofNat d 0) else s.read_data
    let next_read_ptr := if re then s.read_ptr + 1 else s.read_ptr

    -- In Verilog, if both non-blocking assignments trigger, the last one evaluated wins.
    -- Read operation assignment to fifo_count comes after Write operation.
    let next_fifo_count :=
      if re then s.fifo_count - 1
      else if we then s.fifo_count + 1
      else s.fifo_count

    { mem        := next_mem
    , write_ptr  := next_write_ptr
    , read_ptr   := next_read_ptr
    , fifo_count := next_fifo_count
    , read_data  := next_read_data }

def out {d a depth : Nat} (s : State d a depth) : Output d :=
  let fifo_full := s.fifo_count == BitVec.ofNat (a + 1) depth
  let fifo_empty := s.fifo_count == BitVec.ofNat (a + 1) 0
  let high_thresh := BitVec.ofNat (a + 1) ((depth * 80) / 100)
  let low_thresh := BitVec.ofNat (a + 1) ((depth * 20) / 100)

  { read_data              := s.read_data
  , fifo_full              := fifo_full
  , fifo_empty             := fifo_empty
  , high_threshold_reached := s.fifo_count >= high_thresh
  , low_threshold_reached  := s.fifo_count <= low_thresh }

@[simp] theorem step_reset {d a depth : Nat} (s : State d a depth) (we re : Bool) (wd : BitVec d) :
  step s { reset := true, write_enable := we, read_enable := re, write_data := wd } = init := by
  simp [step, init]

@[simp] theorem step_hold {d a depth : Nat} (s : State d a depth) (wd : BitVec d) :
  step s { reset := false, write_enable := false, read_enable := false, write_data := wd } = s := by
  simp [step]

end threshold_fifo
