-- fsm_handshake_3state.lean
import Std

namespace fsm_handshake_3state

inductive FsmState where
  | IDLE
  | WAIT_ACK
  | DONE_ST
deriving Repr, DecidableEq

structure State where
  state : FsmState
deriving Repr, DecidableEq

structure Input where
  rst : Bool
  req : Bool
  ack : Bool
deriving Repr, DecidableEq

structure Output where
  busy : Bool
  done : Bool
deriving Repr, DecidableEq

def init : State :=
  { state := FsmState.IDLE }

def step (s : State) (i : Input) : State :=
  if i.rst then
    init
  else
    match s.state with
    | FsmState.IDLE =>
      if i.req then { state := FsmState.WAIT_ACK } else s
    | FsmState.WAIT_ACK =>
      if i.ack then { state := FsmState.DONE_ST } else s
    | FsmState.DONE_ST =>
      { state := FsmState.IDLE }

def out (s : State) : Output :=
  match s.state with
  | FsmState.IDLE => { busy := false, done := false }
  | FsmState.WAIT_ACK => { busy := true, done := false }
  | FsmState.DONE_ST => { busy := false, done := true }

@[simp] theorem step_reset (s : State) (r a : Bool) :
  step s { rst := true, req := r, ack := a } = init := by
  simp [step, init]

@[simp] theorem step_idle_hold (a : Bool) :
  step { state := FsmState.IDLE } { rst := false, req := false, ack := a } = { state := FsmState.IDLE } := by
  simp [step]

@[simp] theorem step_idle_req (a : Bool) :
  step { state := FsmState.IDLE } { rst := false, req := true, ack := a } = { state := FsmState.WAIT_ACK } := by
  simp [step]

@[simp] theorem step_wait_hold (r : Bool) :
  step { state := FsmState.WAIT_ACK } { rst := false, req := r, ack := false } = { state := FsmState.WAIT_ACK } := by
  simp [step]

@[simp] theorem step_wait_ack (r : Bool) :
  step { state := FsmState.WAIT_ACK } { rst := false, req := r, ack := true } = { state := FsmState.DONE_ST } := by
  simp [step]

@[simp] theorem step_done (r a : Bool) :
  step { state := FsmState.DONE_ST } { rst := false, req := r, ack := a } = { state := FsmState.IDLE } := by
  simp [step]

end fsm_handshake_3state
