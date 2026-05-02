import Std

namespace parallel_prefix_arbiter_v1

structure State (n : Nat) where
  requests_valid : BitVec n
  grant          : BitVec n
deriving Repr, DecidableEq

structure Input (n : Nat) where
  reset : Bool
  req   : BitVec n
deriving Repr, DecidableEq

structure Output (n : Nat) where
  grant : BitVec n
deriving Repr, DecidableEq

def init {n : Nat} : State n :=
  { requests_valid := BitVec.ofNat n 0
  , grant          := BitVec.ofNat n 0 }

def step {n : Nat} (s : State n) (i : Input n) : State n :=
  if i.reset then
    init
  else
    let v := s.requests_valid
    -- The arbiter grants the request with the lowest index (highest priority).
    -- v &&& (~v + 1) isolates the lowest set bit in two's complement arithmetic.
    let next_grant := v &&& ((~~~v) + BitVec.ofNat n 1)
    { requests_valid := i.req
    , grant          := next_grant }

def out {n : Nat} (s : State n) : Output n :=
  { grant := s.grant }

@[simp] theorem step_reset {n : Nat} (s : State n) (r : BitVec n) :
  step s { reset := true, req := r } = init := by
  simp [step, init]

@[simp] theorem step_update {n : Nat} (s : State n) (r : BitVec n) :
  step s { reset := false, req := r } =
  { requests_valid := r
  , grant          := s.requests_valid &&& ((~~~s.requests_valid) + BitVec.ofNat n 1) } := by
  simp [step]

end parallel_prefix_arbiter_v1
