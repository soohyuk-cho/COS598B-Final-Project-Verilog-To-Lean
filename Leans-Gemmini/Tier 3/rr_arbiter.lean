-- rr_arbiter_v1.lean
import Std

namespace rr_arbiter_v1

structure State (n : Nat) where
  grant      : BitVec n
  rotate_ptr : Nat
deriving Repr, DecidableEq

structure Input (n : Nat) where
  rst_n : Bool
  req   : BitVec n
deriving Repr, DecidableEq

structure Output (n : Nat) where
  grant : BitVec n
deriving Repr, DecidableEq

def init {n : Nat} : State n :=
  { grant := BitVec.ofNat n 0
  , rotate_ptr := 0 }

def arbiter_logic {n : Nat} (req : BitVec n) (rotate_ptr : Nat) : Nat → (BitVec n × Nat)
  | 0 => (BitVec.ofNat n 0, rotate_ptr)
  | k + 1 =>
    let i := n - (k + 1)
    let idx := if n = 0 then 0 else (rotate_ptr + i) % n
    if req.getLsb idx then
      (BitVec.ofNat n 1 <<< idx, if n = 0 then 0 else (idx + 1) % n)
    else
      arbiter_logic req rotate_ptr k

def step {n : Nat} (s : State n) (i : Input n) : State n :=
  if !i.rst_n then
    init
  else
    let (grant_next, next_ptr) := arbiter_logic i.req s.rotate_ptr n
    { grant := grant_next
    , rotate_ptr := next_ptr }

def out {n : Nat} (s : State n) : Output n :=
  { grant := s.grant }

@[simp] theorem step_reset {n : Nat} (s : State n) (r : BitVec n) :
  step s { rst_n := false, req := r } = init := by
  simp [step, init]

@[simp] theorem step_update {n : Nat} (s : State n) (r : BitVec n) :
  step s { rst_n := true, req := r } =
  let (g, p) := arbiter_logic r s.rotate_ptr n
  { grant := g, rotate_ptr := p } := by
  simp [step]

end rr_arbiter_v1
