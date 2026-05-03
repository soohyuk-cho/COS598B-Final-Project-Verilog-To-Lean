import Std

namespace token_arbiter_v1

abbrev Bit := Bool
abbrev Bits4 := BitVec 4

structure State where
  token : Bits4
  grant : Bits4
deriving Repr, DecidableEq

structure Input where
  reset : Bit
  req : Bits4
deriving Repr, DecidableEq

structure Output where
  grant : Bits4
deriving Repr, DecidableEq

def bv4 (n : Nat) : Bits4 := BitVec.ofNat 4 n

def init : State :=
  { token := bv4 1
    grant := bv4 0 }

def rotateToken (tok : Bits4) : Bits4 :=
  (tok <<< 1) ||| (tok >>> 3)

def step (s : State) (i : Input) : State :=
  if i.reset then
    init
  else if s.token.getLsb 0 && i.req.getLsb 0 then
    { token := bv4 2, grant := bv4 1 }
  else if s.token.getLsb 1 && i.req.getLsb 1 then
    { token := bv4 4, grant := bv4 2 }
  else if s.token.getLsb 2 && i.req.getLsb 2 then
    { token := bv4 8, grant := bv4 4 }
  else if s.token.getLsb 3 && i.req.getLsb 3 then
    { token := bv4 1, grant := bv4 8 }
  else
    { token := rotateToken s.token, grant := bv4 0 }

def out (s : State) : Output :=
  { grant := s.grant }

@[simp] theorem step_reset (s : State) (r : Bits4) :
    step s { reset := true, req := r } = init := by
  simp [step, init]

@[simp] theorem out_def (s : State) :
    out s = { grant := s.grant } := rfl

theorem step_grant_token0 :
    step { token := bv4 1, grant := bv4 0 } { reset := false, req := bv4 1 } =
      { token := bv4 2, grant := bv4 1 } := by
  native_decide

theorem step_grant_token1 :
    step { token := bv4 2, grant := bv4 0 } { reset := false, req := bv4 2 } =
      { token := bv4 4, grant := bv4 2 } := by
  native_decide

theorem step_grant_token2 :
    step { token := bv4 4, grant := bv4 0 } { reset := false, req := bv4 4 } =
      { token := bv4 8, grant := bv4 4 } := by
  native_decide

theorem step_grant_token3 :
    step { token := bv4 8, grant := bv4 0 } { reset := false, req := bv4 8 } =
      { token := bv4 1, grant := bv4 8 } := by
  native_decide

theorem step_rotate_when_no_matching_request :
    step { token := bv4 2, grant := bv4 0 } { reset := false, req := bv4 1 } =
      { token := bv4 4, grant := bv4 0 } := by
  native_decide

end token_arbiter_v1
