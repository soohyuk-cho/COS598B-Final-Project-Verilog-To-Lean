import Std

namespace sync_fifo

structure State (w d : Nat) where
  buffer       : List (BitVec w)
  rptr         : BitVec d
  wptr         : BitVec d
  full         : Bool
  deq_data_reg : BitVec w
deriving Repr, DecidableEq

structure Input (w : Nat) where
  reset    : Bool
  enq_val  : Bool
  enq_data : BitVec w
  deq_rdy  : Bool
deriving Repr, DecidableEq

structure Output (w : Nat) where
  enq_rdy  : Bool
  deq_val  : Bool
  deq_data : BitVec w
deriving Repr, DecidableEq

def init {w d : Nat} : State w d :=
  { buffer       := List.replicate (2 ^ d) (BitVec.ofNat w 0)
  , rptr         := BitVec.ofNat d 0
  , wptr         := BitVec.ofNat d 0
  , full         := false
  , deq_data_reg := BitVec.ofNat w 0 }

def step {w d : Nat} (s : State w d) (i : Input w) : State w d :=
  if i.reset then
    init
  else
    let enq_rdy := !s.full
    let deq_val := !(s.rptr == s.wptr && !s.full)
    let enq_fire := i.enq_val && enq_rdy
    let deq_fire := i.deq_rdy && deq_val

    if enq_fire then
      { s with
        buffer := s.buffer.set s.wptr.toNat i.enq_data,
        wptr   := s.wptr + 1,
        full   := s.wptr == s.rptr }
    else if deq_fire then
      { s with
        rptr := s.rptr + 1,
        full := false }
    else
      s

def out {w d : Nat} (s : State w d) : Output w :=
  let enq_rdy := !s.full
  let deq_val := !(s.rptr == s.wptr && !s.full)
  let deq_data := s.buffer.getD s.rptr.toNat (BitVec.ofNat w 0)
  { enq_rdy  := enq_rdy
  , deq_val  := deq_val
  , deq_data := deq_data }

@[simp] theorem step_reset {w d : Nat} (s : State w d) (eval drdy : Bool) (edata : BitVec w) :
  step s { reset := true, enq_val := eval, enq_data := edata, deq_rdy := drdy } = init := by
  simp [step, init]

@[simp] theorem step_hold {w d : Nat} (s : State w d) (edata : BitVec w) :
  step s { reset := false, enq_val := false, enq_data := edata, deq_rdy := false } = s := by
  simp [step]

end sync_fifo
