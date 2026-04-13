import Std

namespace fsm_toggle

abbrev Bit := Bool

structure State where
  state : Bit
  deriving Repr, DecidableEq

structure Input where
  rst : Bit
  toggle : Bit
  deriving Repr, DecidableEq

structure Output where
  state_out : Bit
  deriving Repr, DecidableEq

def S0 : Bit := false

def S1 : Bit := true

def init : State := { state := S0 }

def step (s : State) (i : Input) : State :=
  if i.rst then
    init
  else if s.state = S0 then
    if i.toggle then
      { state := S1 }
    else
      { state := S0 }
  else
    if i.toggle then
      { state := S0 }
    else
      { state := S1 }

def out (s : State) : Output :=
  { state_out := s.state }

@[simp] theorem step_reset (s : State) (t : Bit) :
    step s { rst := true, toggle := t } = init := by
  simp [step, init]

@[simp] theorem step_s0_toggle :
    step { state := S0 } { rst := false, toggle := true } = { state := S1 } := by
  simp [step, S0, S1]

@[simp] theorem step_s0_hold :
    step { state := S0 } { rst := false, toggle := false } = { state := S0 } := by
  simp [step, S0, S1]

@[simp] theorem step_s1_toggle :
    step { state := S1 } { rst := false, toggle := true } = { state := S0 } := by
  simp [step, S0, S1]

@[simp] theorem step_s1_hold :
    step { state := S1 } { rst := false, toggle := false } = { state := S1 } := by
  simp [step, S0, S1]

@[simp] theorem step_reset_priority (s : State) :
    step s { rst := true, toggle := true } = init := by
  simp [step, init]

@[simp] theorem out_s0 :
    out { state := S0 } = { state_out := false } := by
  rfl

@[simp] theorem out_s1 :
    out { state := S1 } = { state_out := true } := by
  rfl

end fsm_toggle
