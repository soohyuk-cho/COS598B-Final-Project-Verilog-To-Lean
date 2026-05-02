import Std

namespace shiftreg_right

structure State (w : Nat) where
  data_out : BitVec w
deriving Repr, DecidableEq

structure Input where
  rst      : Bool
  en       : Bool
  shift_in : Bool
deriving Repr, DecidableEq

structure Output (w : Nat) where
  data_out : BitVec w
deriving Repr, DecidableEq

def init {w : Nat} : State w :=
  { data_out := BitVec.ofNat w 0 }

def step {w : Nat} (s : State w) (i : Input) : State w :=
  if i.rst then
    init
  else if i.en then
    let sin_vec := BitVec.ofNat w (if i.shift_in then 1 else 0)
    { data_out := (s.data_out >>> 1) ||| (sin_vec <<< (w - 1)) }
  else
    s

def out {w : Nat} (s : State w) : Output w :=
  { data_out := s.data_out }

@[simp] theorem step_reset {w : Nat} (s : State w) (en sin : Bool) :
  step s { rst := true, en := en, shift_in := sin } = init := by
  simp [step, init]

@[simp] theorem step_hold {w : Nat} (s : State w) (sin : Bool) :
  step s { rst := false, en := false, shift_in := sin } = s := by
  simp [step]

@[simp] theorem step_shift {w : Nat} (s : State w) (sin : Bool) :
  step s { rst := false, en := true, shift_in := sin } =
  { data_out := (s.data_out >>> 1) ||| (BitVec.ofNat w (if sin then 1 else 0) <<< (w - 1)) } := by
  simp [step]

end shiftreg_right
