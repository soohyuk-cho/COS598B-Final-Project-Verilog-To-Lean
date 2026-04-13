import Std

namespace accumulator_en

abbrev Bit := Bool
abbrev Bits8 := BitVec 8

structure State where
  sum_out : Bits8
deriving Repr, DecidableEq

structure Input where
  rst : Bit
  en : Bit
  data_in : Bits8
deriving Repr, DecidableEq

structure Output where
  sum_out : Bits8
deriving Repr, DecidableEq

def bv8 (n : Nat) : Bits8 := BitVec.ofNat 8 n

def init : State := { sum_out := bv8 0 }

-- Synchronous active-high reset with highest priority.
def step (s : State) (i : Input) : State :=
  if i.rst then
    init
  else if i.en then
    { sum_out := s.sum_out + i.data_in }
  else
    { sum_out := s.sum_out }

def out (s : State) : Output :=
  { sum_out := s.sum_out }

@[simp] theorem step_reset (s : State) (en : Bit) (d : Bits8) :
    step s { rst := true, en := en, data_in := d } = init := by
  simp [step, init]

@[simp] theorem step_accumulate (s : State) (d : Bits8) :
    step s { rst := false, en := true, data_in := d } =
      { sum_out := s.sum_out + d } := by
  simp [step]

@[simp] theorem step_hold (s : State) (d : Bits8) :
    step s { rst := false, en := false, data_in := d } =
      { sum_out := s.sum_out } := by
  simp [step]

@[simp] theorem step_reset_priority (s : State) (d : Bits8) :
    step s { rst := true, en := true, data_in := d } = init := by
  simp [step, init]

@[simp] theorem out_sum_out (s : State) :
    out s = { sum_out := s.sum_out } := rfl

end accumulator_en
