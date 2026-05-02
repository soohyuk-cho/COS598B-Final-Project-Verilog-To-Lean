-- fsm_toggle.lean
import Std

namespace fsm_toggle

inductive FsmState where
  | S0
  | S1
deriving Repr, DecidableEq

structure State where
  state : FsmState
deriving Repr, DecidableEq

structure Input where
  rst    : Bool
  toggle : Bool
deriving Repr, DecidableEq

structure Output where
  state_out : Bool
deriving Repr, DecidableEq

def init : State :=
  { state := FsmState.S0 }

def step (s : State) (i : Input) : State :=
  if i.rst then
    init
  else
    match s.state with
    | FsmState.S0 =>
      if i.toggle then { state := FsmState.S1 } else s
    | FsmState.S1 =>
      if i.toggle then { state := FsmState.S0 } else s

def out (s : State) : Output :=
  match s.state with
  | FsmState.S0 => { state_out := false }
  | FsmState.S1 => { state_out := true }

@[simp] theorem step_reset (s : State) (t : Bool) :
  step s { rst := true, toggle := t } = init := by
  simp [step, init]

@[simp] theorem step_hold_S0 :
  step { state := FsmState.S0 } { rst := false, toggle := false } = { state := FsmState.S0 } := by
  simp [step]

@[simp] theorem step_hold_S1 :
  step { state := FsmState.S1 } { rst := false, toggle := false } = { state := FsmState.S1 } := by
  simp [step]

@[simp] theorem step_toggle_S0 :
  step { state := FsmState.S0 } { rst := false, toggle := true } = { state := FsmState.S1 } := by
  simp [step]

@[simp] theorem step_toggle_S1 :
  step { state := FsmState.S1 } { rst := false, toggle := true } = { state := FsmState.S0 } := by
  simp [step]

end fsm_toggle
