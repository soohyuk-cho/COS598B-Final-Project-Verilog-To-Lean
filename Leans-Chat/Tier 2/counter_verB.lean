import Std

namespace counter_loadable

abbrev Bit := Bool
abbrev Bits8 := BitVec 8

structure State where
  count : Bits8
  deriving Repr, DecidableEq

structure Input where
  load : Bit
  en : Bit
  load_value : Bits8
  deriving Repr, DecidableEq

structure Output where
  count : Bits8
  deriving Repr, DecidableEq

def bv8 (n : Nat) : Bits8 := BitVec.ofNat 8 n

def init : State :=
  { count := bv8 0 }

def step (s : State) (rst : Bit) (i : Input) : State :=
  if rst then
    init
  else if i.load then
    { count := i.load_value }
  else if i.en then
    { count := s.count + bv8 1 }
  else
    { count := s.count }

def out (s : State) : Output :=
  { count := s.count }

@[simp] theorem step_reset (s : State) (i : Input) :
    step s true i = init := by
  simp [step, init]

@[simp] theorem step_load (s : State) (v : Bits8) (en : Bit) :
    step s false { load := true, en := en, load_value := v } = { count := v } := by
  simp [step]

@[simp] theorem step_inc (s : State) (v : Bits8) :
    step s false { load := false, en := true, load_value := v } =
      { count := s.count + bv8 1 } := by
  simp [step]

@[simp] theorem step_hold (s : State) (v : Bits8) :
    step s false { load := false, en := false, load_value := v } =
      { count := s.count } := by
  simp [step]

@[simp] theorem step_reset_priority (s : State) (v : Bits8) :
    step s true { load := true, en := true, load_value := v } = init := by
  simp [step, init]

@[simp] theorem out_count (s : State) :
    out s = { count := s.count } := rfl

end counter_loadable
