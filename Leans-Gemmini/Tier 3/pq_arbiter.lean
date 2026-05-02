import Std

namespace pq_arbiter_v1

structure State (n : Nat) where
queue : BitVec n
grant : BitVec n
deriving Repr, DecidableEq

structure Input (n : Nat) where
reset : Bool
req   : BitVec n
deriving Repr, DecidableEq

structure Output (n : Nat) where
grant : BitVec n
deriving Repr, DecidableEq

def init {n : Nat} : State n :=
{ queue := BitVec.ofNat n 0
, grant := BitVec.ofNat n 0 }

def step {n : Nat} (s : State n) (i : Input n) : State n :=
if i.reset then
init
else
let g_mask := s.queue &&& ((~~~s.queue) + BitVec.ofNat n 1)
{ queue := (s.queue ||| i.req) &&& (~~~g_mask)
, grant := g_mask }

def out {n : Nat} (s : State n) : Output n :=
{ grant := s.grant }

@[simp] theorem step_reset {n : Nat} (s : State n) (r : BitVec n) :
step s { reset := true, req := r } = init := by
simp [step, init]

@[simp] theorem step_update {n : Nat} (s : State n) (r : BitVec n) :
step s { reset := false, req := r } =
{ queue := (s.queue ||| r) &&& (~~~(s.queue &&& ((~~~s.queue) + BitVec.ofNat n 1)))
, grant := s.queue &&& ((~~~s.queue) + BitVec.ofNat n 1) } := by
simp [step]

end pq_arbiter_v1
