import Std

namespace divfunc

structure State (xlen : Nat) where
  ready    : List Bool
  dividend : List (BitVec xlen)
  divisor  : List (BitVec xlen)
  quotient : List (BitVec xlen)
deriving Repr, DecidableEq

structure Input (xlen : Nat) where
  rst : Bool
  vld : Bool
  a   : BitVec xlen
  b   : BitVec xlen
deriving Repr, DecidableEq

structure Output (xlen : Nat) where
  quo : BitVec xlen
  rem : BitVec xlen
  ack : Bool
deriving Repr, DecidableEq

def init {xlen : Nat} : State xlen :=
  { ready    := List.replicate (xlen + 1) false
  , dividend := List.replicate (xlen + 1) (BitVec.ofNat xlen 0)
  , divisor  := List.replicate (xlen + 1) (BitVec.ofNat xlen 0)
  , quotient := List.replicate (xlen + 1) (BitVec.ofNat xlen 0) }

def eval_comb {xlen : Nat} (s : State xlen) (stage_list : BitVec xlen) (i : Input xlen) :
  (Array Bool × Array (BitVec xlen) × Array (BitVec xlen) × Array (BitVec xlen) ×
   Array Bool × Array (BitVec xlen) × Array (BitVec xlen) × Array (BitVec xlen)) := Id.run do
  let mut curr_ready := s.ready.toArray
  let mut curr_divd  := s.dividend.toArray
  let mut curr_divs  := s.divisor.toArray
  let mut curr_quo   := s.quotient.toArray

  let mut next_ready := s.ready.toArray
  let mut next_divd  := s.dividend.toArray
  let mut next_divs  := s.divisor.toArray
  let mut next_quo   := s.quotient.toArray

  curr_ready := curr_ready.set! 0 i.vld
  curr_divd  := curr_divd.set! 0 i.a
  curr_divs  := curr_divs.set! 0 i.b
  curr_quo   := curr_quo.set! 0 (BitVec.ofNat xlen 0)

  for idx in [0:xlen] do
    let r_in := curr_ready[idx]!
    let d_in := curr_divd[idx]!
    let v_in := curr_divs[idx]!
    let q_in := curr_quo[idx]!

    let m := d_in >>> (xlen - idx - 1)
    let n := v_in
    let q := if (v_in >>> (idx + 1)) != (BitVec.ofNat xlen 0) then false else (m >= n)
    let t := if q then m - n else m
    let d := (t <<< (xlen - idx - 1)) ||| ((d_in <<< (idx + 1)) >>> (idx + 1))
    let next_q := q_in ||| (if q then (BitVec.ofNat xlen 1 <<< (xlen - idx - 1)) else (BitVec.ofNat xlen 0))

    next_ready := next_ready.set! (idx + 1) r_in
    next_divd  := next_divd.set! (idx + 1) d
    next_divs  := next_divs.set! (idx + 1) v_in
    next_quo   := next_quo.set! (idx + 1) next_q

    let has_ff := stage_list.getLsb (xlen - idx - 1)
    if !has_ff then
      curr_ready := curr_ready.set! (idx + 1) r_in
      curr_divd  := curr_divd.set! (idx + 1) d
      curr_divs  := curr_divs.set! (idx + 1) v_in
      curr_quo   := curr_quo.set! (idx + 1) next_q

  return (curr_ready, curr_divd, curr_divs, curr_quo, next_ready, next_divd, next_divs, next_quo)

def step {xlen : Nat} (stage_list : BitVec xlen) (s : State xlen) (i : Input xlen) : State xlen :=
  if i.rst then
    init
  else
    let (_, _, _, _, n_r, n_d, n_v, n_q) := eval_comb s stage_list i
    { ready    := n_r.toList
    , dividend := n_d.toList
    , divisor  := n_v.toList
    , quotient := n_q.toList }

def out {xlen : Nat} (stage_list : BitVec xlen) (s : State xlen) (i : Input xlen) : Output xlen :=
  let (c_r, c_d, _, c_q, _, _, _, _) := eval_comb s stage_list i
  { quo := c_q[xlen]!
  , rem := c_d[xlen]!
  , ack := c_r[xlen]! }

@[simp] theorem step_reset {xlen : Nat} (stage_list : BitVec xlen) (s : State xlen) (a b : BitVec xlen) (vld : Bool) :
  step stage_list s { rst := true, vld := vld, a := a, b := b } = init := by
  simp [step, init]

end divfunc
