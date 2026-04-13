import Std

namespace accumulator_addsub

def WIDTH : Nat := 8

abbrev Bit := Bool
abbrev Bits := BitVec WIDTH

structure State where
  sum_out : Bits
  deriving Repr, DecidableEq

structure Input where
  rst : Bit
  en : Bit
  sub : Bit
  data_in : Bits
  deriving Repr, DecidableEq

structure Output where
  sum_out : Bits
  deriving Repr, DecidableEq

def bv (n : Nat) : Bits := BitVec.ofNat WIDTH n

def init : State := { sum_out := bv 0 }

def step (s : State) (i : Input) : State :=
  if i.rst then
    init
  else if i.en then
    if i.sub then
      { sum_out := s.sum_out - i.data_in }
    else
      { sum_out := s.sum_out + i.data_in }
  else
    { sum_out := s.sum_out }

def out (s : State) : Output :=
  { sum_out := s.sum_out }

@[simp] theorem step_reset (s : State) (en sub : Bit) (d : Bits) :
    step s { rst := true, en := en, sub := sub, data_in := d } = init := by
  simp [step, init]

@[simp] theorem step_hold (s : State) (sub : Bit) (d : Bits) :
    step s { rst := false, en := false, sub := sub, data_in := d } = { sum_out := s.sum_out } := by
  simp [step]

@[simp] theorem step_add (s : State) (d : Bits) :
    step s { rst := false, en := true, sub := false, data_in := d } =
      { sum_out := s.sum_out + d } := by
  simp [step]

@[simp] theorem step_sub (s : State) (d : Bits) :
    step s { rst := false, en := true, sub := true, data_in := d } =
      { sum_out := s.sum_out - d } := by
  simp [step]

@[simp] theorem step_reset_priority (s : State) (d : Bits) :
    step s { rst := true, en := true, sub := true, data_in := d } = init := by
  simp [step, init]

@[simp] theorem out_sum_out (s : State) :
    out s = { sum_out := s.sum_out } := rfl

end accumulator_addsub
