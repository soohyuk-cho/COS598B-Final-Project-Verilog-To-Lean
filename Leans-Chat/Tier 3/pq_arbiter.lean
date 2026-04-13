import Std

namespace pq_arbiter_v1

abbrev Bit := Bool
abbrev Bits4 := BitVec 4

structure State where
  q0 : Bits4
  q1 : Bits4
  q2 : Bits4
  q3 : Bits4
  head0 : Int
  tail0 : Int
  head1 : Int
  tail1 : Int
  head2 : Int
  tail2 : Int
  head3 : Int
  tail3 : Int
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

def bitAt (x : Bits4) (idx : Nat) : Bool :=
  ((x.toNat / (2 ^ idx)) % 2) == 1

def clearBitNat (n idx : Nat) : Nat :=
  if ((n / (2 ^ idx)) % 2) == 1 then n - (2 ^ idx) else n

def setBitTo (x : Bits4) (idx : Nat) (b : Bool) : Bits4 :=
  let cleared := clearBitNat x.toNat idx
  bv4 (if b then cleared + (2 ^ idx) else cleared)

def grantVec (idx? : Option Nat) : Bits4 :=
  match idx? with
  | some 0 => bv4 1
  | some 1 => bv4 2
  | some 2 => bv4 4
  | some 3 => bv4 8
  | _ => bv4 0

def init : State :=
  { q0 := bv4 0
    q1 := bv4 0
    q2 := bv4 0
    q3 := bv4 0
    head0 := 0
    tail0 := 0
    head1 := 0
    tail1 := 0
    head2 := 0
    tail2 := 0
    head3 := 0
    tail3 := 0
    grant := bv4 0 }

def step (s : State) (i : Input) : State :=
  if i.reset then
    init
  else
    let p0 := bitAt s.q0 0
    let p1 := bitAt s.q1 1
    let p2 := bitAt s.q2 2
    let p3 := bitAt s.q3 3
    let q0' := if bitAt i.req 0 && !p0 then setBitTo s.q0 0 true else s.q0
    let q1' := if bitAt i.req 1 && !p1 then setBitTo s.q1 1 true else s.q1
    let q2' := if bitAt i.req 2 && !p2 then setBitTo s.q2 2 true else s.q2
    let q3' := if bitAt i.req 3 && !p3 then setBitTo s.q3 3 true else s.q3
    let g? :=
      if p0 then some 0
      else if p1 then some 1
      else if p2 then some 2
      else if p3 then some 3
      else none
    { q0 := if g? = some 0 then setBitTo q0' 0 false else q0'
      q1 := if g? = some 1 then setBitTo q1' 1 false else q1'
      q2 := if g? = some 2 then setBitTo q2' 2 false else q2'
      q3 := if g? = some 3 then setBitTo q3' 3 false else q3'
      head0 := s.head0
      tail0 := s.tail0
      head1 := s.head1
      tail1 := s.tail1
      head2 := s.head2
      tail2 := s.tail2
      head3 := s.head3
      tail3 := s.tail3
      grant := grantVec g? }

def out (s : State) : Output :=
  { grant := s.grant }

@[simp] theorem step_reset (s : State) (r : Bits4) :
    step s { reset := true, req := r } = init := by
  simp [step, init]

@[simp] theorem out_def (s : State) :
    out s = { grant := s.grant } := rfl

theorem step_hold_empty :
    step init { reset := false, req := bv4 0 } = init := by
  native_decide

theorem step_enqueue_req2_from_empty :
    step init { reset := false, req := bv4 4 } =
      { q0 := bv4 0
        q1 := bv4 0
        q2 := bv4 4
        q3 := bv4 0
        head0 := 0
        tail0 := 0
        head1 := 0
        tail1 := 0
        head2 := 0
        tail2 := 0
        head3 := 0
        tail3 := 0
        grant := bv4 0 } := by
  native_decide

theorem step_grant_from_q1 :
    step
      { q0 := bv4 0
        q1 := bv4 2
        q2 := bv4 4
        q3 := bv4 0
        head0 := 0
        tail0 := 0
        head1 := 0
        tail1 := 0
        head2 := 0
        tail2 := 0
        head3 := 0
        tail3 := 0
        grant := bv4 0 }
      { reset := false, req := bv4 0 } =
      { q0 := bv4 0
        q1 := bv4 0
        q2 := bv4 4
        q3 := bv4 0
        head0 := 0
        tail0 := 0
        head1 := 0
        tail1 := 0
        head2 := 0
        tail2 := 0
        head3 := 0
        tail3 := 0
        grant := bv4 2 } := by
  native_decide

theorem step_priority_prefers_lower_index :
    step
      { q0 := bv4 1
        q1 := bv4 2
        q2 := bv4 4
        q3 := bv4 8
        head0 := 0
        tail0 := 0
        head1 := 0
        tail1 := 0
        head2 := 0
        tail2 := 0
        head3 := 0
        tail3 := 0
        grant := bv4 0 }
      { reset := false, req := bv4 0 } =
      { q0 := bv4 0
        q1 := bv4 2
        q2 := bv4 4
        q3 := bv4 8
        head0 := 0
        tail0 := 0
        head1 := 0
        tail1 := 0
        head2 := 0
        tail2 := 0
        head3 := 0
        tail3 := 0
        grant := bv4 1 } := by
  native_decide

theorem step_enqueue_and_grant_use_old_queue_state :
    step
      { q0 := bv4 0
        q1 := bv4 0
        q2 := bv4 4
        q3 := bv4 0
        head0 := 0
        tail0 := 0
        head1 := 0
        tail1 := 0
        head2 := 0
        tail2 := 0
        head3 := 0
        tail3 := 0
        grant := bv4 0 }
      { reset := false, req := bv4 1 } =
      { q0 := bv4 1
        q1 := bv4 0
        q2 := bv4 0
        q3 := bv4 0
        head0 := 0
        tail0 := 0
        head1 := 0
        tail1 := 0
        head2 := 0
        tail2 := 0
        head3 := 0
        tail3 := 0
        grant := bv4 4 } := by
  native_decide

end pq_arbiter_v1
