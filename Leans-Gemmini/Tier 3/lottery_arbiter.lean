import Std

namespace lottery_arbiter

structure State where
  rand_num : BitVec 4
deriving Repr, DecidableEq

structure Input where
  rst_n     : Bool
  req       : BitVec 4
  next_rand : BitVec 4
deriving Repr, DecidableEq

structure Output where
  grant : BitVec 4
deriving Repr, DecidableEq

def init : State :=
  { rand_num := BitVec.ofNat 4 0 }

def step (s : State) (i : Input) : State :=
  if !i.rst_n then
    init
  else
    { rand_num := i.next_rand }

def out (s : State) (i : Input) : Output :=
  let r := s.rand_num.toNat
  let g0 := if r < 1 then (if i.req.getLsb 0 then 1 else 0) else 0
  let g1 := if r ≥ 1 ∧ r < 3 then (if i.req.getLsb 1 then 2 else 0) else 0
  let g2 := if r ≥ 3 ∧ r < 6 then (if i.req.getLsb 2 then 4 else 0) else 0
  let g3 := if r ≥ 6 ∧ r < 10 then (if i.req.getLsb 3 then 8 else 0) else 0
  { grant := BitVec.ofNat 4 (g0 + g1 + g2 + g3) }

@[simp] theorem step_reset (s : State) (r nr : BitVec 4) :
  step s { rst_n := false, req := r, next_rand := nr } = init := by
  simp [step, init]

@[simp] theorem step_update (s : State) (r nr : BitVec 4) :
  step s { rst_n := true, req := r, next_rand := nr } = { rand_num := nr } := by
  simp [step]

end lottery_arbiter
