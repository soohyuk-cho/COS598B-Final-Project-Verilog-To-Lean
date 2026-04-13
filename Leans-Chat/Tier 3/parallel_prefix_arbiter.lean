import Std

namespace parallel_prefix_arbiter_v1

abbrev Bit := Bool
abbrev Bits8 := BitVec 8
abbrev Bits32 := BitVec 32

structure State where
  req_valids : Bits8
  priorities : Array Bits32
  grant : Bits8
  deriving Repr, DecidableEq

structure Input where
  reset : Bit
  req : Bits8
  deriving Repr, DecidableEq

structure Output where
  grant : Bits8
  deriving Repr, DecidableEq

def bv8 (n : Nat) : Bits8 := BitVec.ofNat 8 n

def bv32 (n : Nat) : Bits32 := BitVec.ofNat 32 n

def initPriorities : Array Bits32 :=
  #[bv32 0, bv32 1, bv32 2, bv32 3, bv32 4, bv32 5, bv32 6, bv32 7]

def init : State :=
  { req_valids := bv8 0
    priorities := initPriorities
    grant := bv8 0 }

-- Lower index means higher priority.
def reqBit (req : Bits8) (idx : Nat) : Bool :=
  ((req.toNat / (2 ^ idx)) % 2) == 1

def grantNat (req_valids : Bits8) : Nat :=
  if reqBit req_valids 0 then 1
  else if reqBit req_valids 1 then 2
  else if reqBit req_valids 2 then 4
  else if reqBit req_valids 3 then 8
  else if reqBit req_valids 4 then 16
  else if reqBit req_valids 5 then 32
  else if reqBit req_valids 6 then 64
  else if reqBit req_valids 7 then 128
  else 0

def grantOf (req_valids : Bits8) : Bits8 :=
  bv8 (grantNat req_valids)

-- The RTL updates requests[i].valid with nonblocking assignments, while the
-- grant computation uses the old registered request validity from the current
-- state. The priority array is reset to its index values and otherwise held.
def step (s : State) (i : Input) : State :=
  if i.reset then
    init
  else
    { req_valids := i.req
      priorities := s.priorities
      grant := grantOf s.req_valids }

def out (s : State) : Output :=
  { grant := s.grant }

@[simp] theorem step_reset (s : State) (q : Bits8) :
    step s { reset := true, req := q } = init := by
  simp [step, init]

@[simp] theorem step_update (s : State) (q : Bits8) :
    step s { reset := false, req := q } =
      { req_valids := q, priorities := s.priorities, grant := grantOf s.req_valids } := by
  simp [step]

@[simp] theorem out_def (s : State) :
    out s = { grant := s.grant } := rfl

theorem grantOf_none :
    grantOf (bv8 0) = bv8 0 := by
  native_decide

theorem grantOf_req0 :
    grantOf (bv8 1) = bv8 1 := by
  native_decide

theorem grantOf_req2 :
    grantOf (bv8 4) = bv8 4 := by
  native_decide

theorem grantOf_lowest_index_wins :
    grantOf (bv8 13) = bv8 1 := by
  native_decide

theorem step_uses_previous_registered_requests :
    step
      { req_valids := bv8 4, priorities := initPriorities, grant := bv8 0 }
      { reset := false, req := bv8 1 } =
      { req_valids := bv8 1, priorities := initPriorities, grant := bv8 4 } := by
  native_decide

end parallel_prefix_arbiter_v1
