import Std

namespace rr_arbiter_v1

abbrev Bit := Bool
abbrev Bits2 := BitVec 2
abbrev Bits4 := BitVec 4

structure State where
  rotate_ptr : Bits2
  grant : Bits4
  deriving Repr, DecidableEq

structure Input where
  rst_n : Bit
  req : Bits4
  deriving Repr, DecidableEq

structure Output where
  grant : Bits4
  deriving Repr, DecidableEq

def bv2 (n : Nat) : Bits2 := BitVec.ofNat 2 n

def bv4 (n : Nat) : Bits4 := BitVec.ofNat 4 n

def init : State :=
  { rotate_ptr := bv2 0
    grant := bv4 0 }

def reqBit (req : Bits4) (idx : Nat) : Bool :=
  ((req.toNat / (2 ^ idx)) % 2) == 1

def firstGrantIdx (rotate_ptr : Bits2) (req : Bits4) : Option Nat :=
  let p := rotate_ptr.toNat
  let i0 := p % 4
  let i1 := (p + 1) % 4
  let i2 := (p + 2) % 4
  let i3 := (p + 3) % 4
  if reqBit req i0 then some i0
  else if reqBit req i1 then some i1
  else if reqBit req i2 then some i2
  else if reqBit req i3 then some i3
  else none

def grantOfIdx : Option Nat -> Bits4
  | some 0 => bv4 1
  | some 1 => bv4 2
  | some 2 => bv4 4
  | some 3 => bv4 8
  | _ => bv4 0

def nextPtr (rotate_ptr : Bits2) (idx? : Option Nat) : Bits2 :=
  match idx? with
  | some idx => bv2 ((idx + 1) % 4)
  | none => rotate_ptr

def step (s : State) (i : Input) : State :=
  if !i.rst_n then
    init
  else
    let idx? := firstGrantIdx s.rotate_ptr i.req
    let grant_next := grantOfIdx idx?
    let next_ptr := nextPtr s.rotate_ptr idx?
    { rotate_ptr := if grant_next = bv4 0 then s.rotate_ptr else next_ptr
      grant := grant_next }

def out (s : State) : Output :=
  { grant := s.grant }

@[simp] theorem step_reset (s : State) (r : Bits4) :
    step s { rst_n := false, req := r } = init := by
  simp [step, init]

@[simp] theorem step_no_request (s : State) :
    step s { rst_n := true, req := bv4 0 } =
      { rotate_ptr := s.rotate_ptr, grant := bv4 0 } := by
  simp [step, firstGrantIdx, grantOfIdx, nextPtr, reqBit, bv4]

@[simp] theorem out_def (s : State) :
    out s = { grant := s.grant } := rfl

theorem step_grant_req0_from_reset :
    step init { rst_n := true, req := bv4 1 } =
      { rotate_ptr := bv2 1, grant := bv4 1 } := by
  native_decide

theorem step_grant_req2_from_ptr1 :
    step { rotate_ptr := bv2 1, grant := bv4 0 } { rst_n := true, req := bv4 4 } =
      { rotate_ptr := bv2 3, grant := bv4 4 } := by
  native_decide

theorem step_wraparound_grant_req0_from_ptr3 :
    step { rotate_ptr := bv2 3, grant := bv4 0 } { rst_n := true, req := bv4 1 } =
      { rotate_ptr := bv2 1, grant := bv4 1 } := by
  native_decide

theorem step_priority_from_rotate_ptr2 :
    step { rotate_ptr := bv2 2, grant := bv4 0 } { rst_n := true, req := bv4 9 } =
      { rotate_ptr := bv2 0, grant := bv4 8 } := by
  native_decide

end rr_arbiter_v1
