import Std

namespace sync_fifo

abbrev Bit := Bool
abbrev Bits32 := BitVec 32
abbrev Bits3 := BitVec 3

def DEPTH : Nat := 8

def bv32 (n : Nat) : Bits32 := BitVec.ofNat 32 n

def bv3 (n : Nat) : Bits3 := BitVec.ofNat 3 n

structure State where
  buffer : Array Bits32
  rptr : Bits3
  wptr : Bits3
  full : Bit
  deq_data_reg : Bits32
  deriving Repr, DecidableEq

structure Input where
  enq_val : Bit
  enq_data : Bits32
  deq_rdy : Bit
  deriving Repr, DecidableEq

structure Output where
  enq_rdy : Bit
  deq_val : Bit
  deq_data : Bits32
  deriving Repr, DecidableEq

def init : State :=
  { buffer := Array.replicate DEPTH (bv32 0)
    rptr := bv3 0
    wptr := bv3 0
    full := false
    deq_data_reg := bv32 0 }

def ptrIdx (p : Bits3) : Nat :=
  p.toNat

def enq_rdy (s : State) : Bit :=
  !s.full

def deq_val (s : State) : Bit :=
  !((decide (s.rptr = s.wptr)) && (!s.full))

def deq_data (s : State) : Bits32 :=
  s.buffer.getD (ptrIdx s.rptr) (bv32 0)

def enq_fire (s : State) (i : Input) : Bit :=
  i.enq_val && enq_rdy s

def deq_fire (s : State) (i : Input) : Bit :=
  deq_val s && i.deq_rdy

def step (reset : Bit) (s : State) (i : Input) : State :=
  if reset then
    { buffer := s.buffer
      rptr := bv3 0
      wptr := bv3 0
      full := false
      deq_data_reg := bv32 0 }
  else if enq_fire s i then
    { buffer := s.buffer.set! (ptrIdx s.wptr) i.enq_data
      rptr := s.rptr
      wptr := s.wptr + bv3 1
      full := if s.wptr = s.rptr then true else false
      deq_data_reg := s.deq_data_reg }
  else if deq_fire s i then
    { buffer := s.buffer
      rptr := s.rptr + bv3 1
      wptr := s.wptr
      full := false
      deq_data_reg := s.deq_data_reg }
  else
    s

def out (s : State) : Output :=
  { enq_rdy := enq_rdy s
    deq_val := deq_val s
    deq_data := deq_data s }

@[simp] theorem step_reset (s : State) (i : Input) :
    step true s i =
      { buffer := s.buffer
        rptr := bv3 0
        wptr := bv3 0
        full := false
        deq_data_reg := bv32 0 } := by
  simp [step]

@[simp] theorem step_hold (s : State) (d : Bits32) :
    step false s { enq_val := false, enq_data := d, deq_rdy := false } = s := by
  simp [step, enq_fire, deq_fire, enq_rdy, deq_val]

@[simp] theorem step_enq (s : State) (d : Bits32) (h : s.full = false) :
    step false s { enq_val := true, enq_data := d, deq_rdy := false } =
      { buffer := s.buffer.set! (ptrIdx s.wptr) d
        rptr := s.rptr
        wptr := s.wptr + bv3 1
        full := if s.wptr = s.rptr then true else false
        deq_data_reg := s.deq_data_reg } := by
  simp [step, enq_fire, enq_rdy, h]

@[simp] theorem step_deq (s : State) (d : Bits32) (h : deq_val s = true) :
    step false s { enq_val := false, enq_data := d, deq_rdy := true } =
      { buffer := s.buffer
        rptr := s.rptr + bv3 1
        wptr := s.wptr
        full := false
        deq_data_reg := s.deq_data_reg } := by
  simp [step, enq_fire, deq_fire, h]

@[simp] theorem step_enq_priority (s : State) (d : Bits32) (h : s.full = false) :
    step false s { enq_val := true, enq_data := d, deq_rdy := true } =
      { buffer := s.buffer.set! (ptrIdx s.wptr) d
        rptr := s.rptr
        wptr := s.wptr + bv3 1
        full := if s.wptr = s.rptr then true else false
        deq_data_reg := s.deq_data_reg } := by
  simp [step, enq_fire, enq_rdy, h]

@[simp] theorem out_init :
    out init = { enq_rdy := true, deq_val := false, deq_data := bv32 0 } := by
  native_decide

end sync_fifo
