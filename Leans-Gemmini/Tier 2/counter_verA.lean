-- counter_wrap.lean
import Std

namespace counter_wrap

structure State (w : Nat) where
  count : BitVec w
deriving Repr, DecidableEq

structure Input where
  rst : Bool
  en  : Bool
deriving Repr, DecidableEq

structure Output (w : Nat) where
  count : BitVec w
deriving Repr, DecidableEq

def init {w : Nat} : State w :=
  { count := BitVec.ofNat w 0 }

def step {w : Nat} (s : State w) (i : Input) : State w :=
  if i.rst then
    init
  else if i.en then
    { count := s.count + 1 }
  else
    s

def out {w : Nat} (s : State w) : Output w :=
  { count := s.count }

@[simp] theorem step_reset {w : Nat} (s : State w) (en : Bool) :
  step s { rst := true, en := en } = init := by
  simp [step, init]

@[simp] theorem step_hold {w : Nat} (s : State w) :
  step s { rst := false, en := false } = s := by
  simp [step]

@[simp] theorem step_inc {w : Nat} (s : State w) :
  step s { rst := false, en := true } = { count := s.count + 1 } := by
  simp [step]

end counter_wrap
