import Std

namespace counter_wrap

abbrev Bit := Bool
abbrev Bits8 := BitVec 8

structure State where
  count : Bits8
deriving Repr, DecidableEq

structure Input where
  rst : Bit
  en : Bit
deriving Repr, DecidableEq

structure Output where
  count : Bits8
deriving Repr, DecidableEq

def bv8 (n : Nat) : Bits8 := BitVec.ofNat 8 n

def init : State :=
  { count := bv8 0 }

def step (s : State) (i : Input) : State :=
  if i.rst then
    init
  else if i.en then
    { count := s.count + bv8 1 }
  else
    { count := s.count }

def out (s : State) : Output :=
  { count := s.count }

@[simp] theorem step_reset (s : State) (en : Bit) :
    step s { rst := true, en := en } = init := by
  simp [step, init]

@[simp] theorem step_reset_priority (s : State) :
    step s { rst := true, en := true } = init := by
  simp [step, init]

@[simp] theorem step_inc (s : State) :
    step s { rst := false, en := true } = { count := s.count + bv8 1 } := by
  simp [step]

@[simp] theorem step_hold (s : State) :
    step s { rst := false, en := false } = { count := s.count } := by
  simp [step]

@[simp] theorem out_count (s : State) :
    out s = { count := s.count } := rfl

theorem step_wraparound_max :
    step { count := bv8 255 } { rst := false, en := true } = { count := bv8 0 } := by
  native_decide

end counter_wrap
