-- accumulator_addsub.lean
import Std

namespace accumulator_addsub

structure State (w : Nat) where
  sum_out : BitVec w
deriving Repr, DecidableEq

structure Input (w : Nat) where
  rst     : Bool
  en      : Bool
  sub     : Bool
  data_in : BitVec w
deriving Repr, DecidableEq

structure Output (w : Nat) where
  sum_out : BitVec w
deriving Repr, DecidableEq

def init {w : Nat} : State w :=
  { sum_out := BitVec.ofNat w 0 }

def step {w : Nat} (s : State w) (i : Input w) : State w :=
  if i.rst then
    init
  else if i.en then
    if i.sub then
      { sum_out := s.sum_out - i.data_in }
    else
      { sum_out := s.sum_out + i.data_in }
  else
    s

def out {w : Nat} (s : State w) : Output w :=
  { sum_out := s.sum_out }

@[simp] theorem step_reset {w : Nat} (s : State w) (en sub : Bool) (d : BitVec w) :
  step s { rst := true, en := en, sub := sub, data_in := d } = init := by
  simp [step, init]

@[simp] theorem step_hold {w : Nat} (s : State w) (sub : Bool) (d : BitVec w) :
  step s { rst := false, en := false, sub := sub, data_in := d } = s := by
  simp [step]

@[simp] theorem step_add {w : Nat} (s : State w) (d : BitVec w) :
  step s { rst := false, en := true, sub := false, data_in := d } = { sum_out := s.sum_out + d } := by
  simp [step]

@[simp] theorem step_sub {w : Nat} (s : State w) (d : BitVec w) :
  step s { rst := false, en := true, sub := true, data_in := d } = { sum_out := s.sum_out - d } := by
  simp [step]

end accumulator_addsub
