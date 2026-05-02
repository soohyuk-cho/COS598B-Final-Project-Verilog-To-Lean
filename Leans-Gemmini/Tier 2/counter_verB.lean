import Std

namespace counter_loadable

structure State (w : Nat) where
  count : BitVec w
deriving Repr, DecidableEq

structure Input (w : Nat) where
  rst        : Bool
  load       : Bool
  en         : Bool
  load_value : BitVec w
deriving Repr, DecidableEq

structure Output (w : Nat) where
  count : BitVec w
deriving Repr, DecidableEq

def init {w : Nat} : State w :=
  { count := BitVec.ofNat w 0 }

def step {w : Nat} (s : State w) (i : Input w) : State w :=
  if i.rst then
    init
  else if i.load then
    { count := i.load_value }
  else if i.en then
    { count := s.count + 1 }
  else
    s

def out {w : Nat} (s : State w) : Output w :=
  { count := s.count }

@[simp] theorem step_reset {w : Nat} (s : State w) (load en : Bool) (v : BitVec w) :
  step s { rst := true, load := load, en := en, load_value := v } = init := by
  simp [step, init]

@[simp] theorem step_load {w : Nat} (s : State w) (en : Bool) (v : BitVec w) :
  step s { rst := false, load := true, en := en, load_value := v } = { count := v } := by
  simp [step]

@[simp] theorem step_en {w : Nat} (s : State w) (v : BitVec w) :
  step s { rst := false, load := false, en := true, load_value := v } = { count := s.count + 1 } := by
  simp [step]

@[simp] theorem step_hold {w : Nat} (s : State w) (v : BitVec w) :
  step s { rst := false, load := false, en := false, load_value := v } = s := by
  simp [step]

end counter_loadable
