import Std

namespace shiftreg_right

abbrev Bit := Bool
abbrev Bits8 := BitVec 8

structure State where
  data_out : Bits8
deriving Repr, DecidableEq

structure Input where
  rst : Bit
  en : Bit
  shift_in : Bit
deriving Repr, DecidableEq

structure Output where
  data_out : Bits8
deriving Repr, DecidableEq

def bv8 (n : Nat) : Bits8 := BitVec.ofNat 8 n

def init : State :=
  { data_out := bv8 0 }

def shiftRightInsert (x : Bits8) (b : Bit) : Bits8 :=
  bv8 (((if b then 128 else 0) + (x.toNat / 2)) % 256)

def step (s : State) (i : Input) : State :=
  if i.rst then
    init
  else if i.en then
    { data_out := shiftRightInsert s.data_out i.shift_in }
  else
    { data_out := s.data_out }

def out (s : State) : Output :=
  { data_out := s.data_out }

@[simp] theorem step_reset (s : State) (en shift_in : Bit) :
    step s { rst := true, en := en, shift_in := shift_in } = init := by
  simp [step, init]

@[simp] theorem step_reset_priority (s : State) :
    step s { rst := true, en := true, shift_in := true } = init := by
  simp [step, init]

@[simp] theorem step_shift (s : State) (b : Bit) :
    step s { rst := false, en := true, shift_in := b } =
      { data_out := shiftRightInsert s.data_out b } := by
  simp [step]

@[simp] theorem step_hold (s : State) (b : Bit) :
    step s { rst := false, en := false, shift_in := b } =
      { data_out := s.data_out } := by
  simp [step]

@[simp] theorem out_data_out (s : State) :
    out s = { data_out := s.data_out } := rfl

theorem step_shift_example_one :
    step { data_out := bv8 10 } { rst := false, en := true, shift_in := true } =
      { data_out := bv8 133 } := by
  native_decide

theorem step_shift_example_zero :
    step { data_out := bv8 11 } { rst := false, en := true, shift_in := false } =
      { data_out := bv8 5 } := by
  native_decide

end shiftreg_right
