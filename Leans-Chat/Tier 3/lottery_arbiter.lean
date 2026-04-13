import Std

namespace lottery_arbiter

abbrev Bit := Bool
abbrev Bits4 := BitVec 4

structure State where
  rand_num : Bits4
  req : Bits4
  deriving Repr, DecidableEq

structure Input where
  rst_n : Bit
  req : Bits4
  rand_sample : Bits4
  deriving Repr, DecidableEq

structure Output where
  grant : Bits4
  deriving Repr, DecidableEq

def bv4 (n : Nat) : Bits4 := BitVec.ofNat 4 n

def init : State :=
  { rand_num := bv4 0
    req := bv4 0 }

def reqBit (req : Bits4) (idx : Nat) : Bool :=
  ((req.toNat / (2 ^ idx)) % 2) == 1

def grantNat (rand_num req : Bits4) : Nat :=
  let r := rand_num.toNat
  let g0 := if (r == 0) && reqBit req 0 then 1 else 0
  let g1 := if ((r == 1) || (r == 2)) && reqBit req 1 then 2 else 0
  let g2 := if ((r == 3) || (r == 4) || (r == 5)) && reqBit req 2 then 4 else 0
  let g3 := if ((r == 6) || (r == 7) || (r == 8) || (r == 9)) && reqBit req 3 then 8 else 0
  g0 + g1 + g2 + g3

def grantOf (rand_num req : Bits4) : Bits4 :=
  bv4 (grantNat rand_num req)

def step (s : State) (i : Input) : State :=
  if !i.rst_n then
    init
  else
    { rand_num := i.rand_sample
      req := i.req }

def out (s : State) : Output :=
  { grant := grantOf s.rand_num s.req }

@[simp] theorem step_reset (s : State) (q r : Bits4) :
    step s { rst_n := false, req := q, rand_sample := r } = init := by
  simp [step, init]

@[simp] theorem step_update (s : State) (q r : Bits4) :
    step s { rst_n := true, req := q, rand_sample := r } =
      { rand_num := r, req := q } := by
  simp [step]

@[simp] theorem out_def (s : State) :
    out s = { grant := grantOf s.rand_num s.req } := rfl

theorem out_grant_req0 :
    out { rand_num := bv4 0, req := bv4 1 } = { grant := bv4 1 } := by
  native_decide

theorem out_grant_req1_ticket1 :
    out { rand_num := bv4 1, req := bv4 2 } = { grant := bv4 2 } := by
  native_decide

theorem out_grant_req1_ticket2 :
    out { rand_num := bv4 2, req := bv4 2 } = { grant := bv4 2 } := by
  native_decide

theorem out_grant_req2_ticket3 :
    out { rand_num := bv4 3, req := bv4 4 } = { grant := bv4 4 } := by
  native_decide

theorem out_grant_req3_ticket6 :
    out { rand_num := bv4 6, req := bv4 8 } = { grant := bv4 8 } := by
  native_decide

theorem out_no_grant_when_unrequested :
    out { rand_num := bv4 2, req := bv4 0 } = { grant := bv4 0 } := by
  native_decide

end lottery_arbiter
