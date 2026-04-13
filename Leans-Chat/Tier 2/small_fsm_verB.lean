import Std

namespace fsm_handshake_3state

abbrev Bit := Bool
abbrev Bits2 := BitVec 2

structure State where
  state : Bits2
  deriving Repr, DecidableEq

structure Input where
  rst : Bit
  req : Bit
  ack : Bit
  deriving Repr, DecidableEq

structure Output where
  busy : Bit
  done : Bit
  deriving Repr, DecidableEq

def bv2 (n : Nat) : Bits2 := BitVec.ofNat 2 n

def IDLE : Bits2 := bv2 0

def WAIT_ACK : Bits2 := bv2 1

def DONE_ST : Bits2 := bv2 2

def init : State := { state := IDLE }

def step (s : State) (i : Input) : State :=
  if i.rst then
    init
  else if s.state = IDLE then
    if i.req then
      { state := WAIT_ACK }
    else
      { state := IDLE }
  else if s.state = WAIT_ACK then
    if i.ack then
      { state := DONE_ST }
    else
      { state := WAIT_ACK }
  else if s.state = DONE_ST then
    { state := IDLE }
  else
    { state := IDLE }

def out (s : State) : Output :=
  if s.state = IDLE then
    { busy := false, done := false }
  else if s.state = WAIT_ACK then
    { busy := true, done := false }
  else if s.state = DONE_ST then
    { busy := false, done := true }
  else
    { busy := false, done := false }

@[simp] theorem step_reset (s : State) (req ack : Bit) :
    step s { rst := true, req := req, ack := ack } = init := by
  simp [step, init]

@[simp] theorem step_idle_to_wait (ack : Bit) :
    step { state := IDLE } { rst := false, req := true, ack := ack } = { state := WAIT_ACK } := by
  simp [step, IDLE, WAIT_ACK, DONE_ST, bv2]

@[simp] theorem step_idle_hold (ack : Bit) :
    step { state := IDLE } { rst := false, req := false, ack := ack } = { state := IDLE } := by
  simp [step, IDLE, WAIT_ACK, DONE_ST, bv2]

@[simp] theorem step_wait_to_done (req : Bit) :
    step { state := WAIT_ACK } { rst := false, req := req, ack := true } = { state := DONE_ST } := by
  simp [step, IDLE, WAIT_ACK, DONE_ST, bv2]

@[simp] theorem step_wait_hold (req : Bit) :
    step { state := WAIT_ACK } { rst := false, req := req, ack := false } = { state := WAIT_ACK } := by
  simp [step, IDLE, WAIT_ACK, DONE_ST, bv2]

@[simp] theorem step_done_to_idle (req ack : Bit) :
    step { state := DONE_ST } { rst := false, req := req, ack := ack } = { state := IDLE } := by
  simp [step, IDLE, WAIT_ACK, DONE_ST, bv2]

@[simp] theorem step_default_to_idle (req ack : Bit) :
    step { state := bv2 3 } { rst := false, req := req, ack := ack } = { state := IDLE } := by
  simp [step, IDLE, WAIT_ACK, DONE_ST, bv2]

@[simp] theorem out_idle :
    out { state := IDLE } = { busy := false, done := false } := by
  simp [out, IDLE, WAIT_ACK, DONE_ST, bv2]

@[simp] theorem out_wait_ack :
    out { state := WAIT_ACK } = { busy := true, done := false } := by
  simp [out, IDLE, WAIT_ACK, DONE_ST, bv2]

@[simp] theorem out_done_st :
    out { state := DONE_ST } = { busy := false, done := true } := by
  simp [out, IDLE, WAIT_ACK, DONE_ST, bv2]

@[simp] theorem out_default :
    out { state := bv2 3 } = { busy := false, done := false } := by
  simp [out, IDLE, WAIT_ACK, DONE_ST, bv2]

end fsm_handshake_3state
