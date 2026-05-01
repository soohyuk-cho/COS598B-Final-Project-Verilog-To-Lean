import Std

namespace divfunc

abbrev Bit := Bool
abbrev Bits (n : Nat) := BitVec n

def pow2 (n : Nat) : Nat := 2 ^ n

def bv (n : Nat) (x : Nat) : BitVec n := BitVec.ofNat n x

structure State (XLEN : Nat) where
  ready : Array Bit
  dividend : Array (Bits XLEN)
  divisor : Array (Bits XLEN)
  quotient : Array (Bits XLEN)
deriving Repr, DecidableEq

structure Input (XLEN : Nat) where
  rst : Bit
  a : Bits XLEN
  b : Bits XLEN
  vld : Bit
deriving Repr, DecidableEq

structure Output (XLEN : Nat) where
  quo : Bits XLEN
  rem : Bits XLEN
  ack : Bit
deriving Repr, DecidableEq

structure StageVals (XLEN : Nat) where
  ready : Bit
  dividend : Bits XLEN
  divisor : Bits XLEN
  quotient : Bits XLEN
deriving Repr, DecidableEq

def init {XLEN : Nat} : State XLEN :=
  { ready := Array.replicate (XLEN + 1) false
    dividend := Array.replicate (XLEN + 1) (bv XLEN 0)
    divisor := Array.replicate (XLEN + 1) (bv XLEN 0)
    quotient := Array.replicate (XLEN + 1) (bv XLEN 0) }

def stageEnabled {XLEN : Nat} (stageList : Bits XLEN) (bit : Nat) : Bit :=
  decide (((stageList.toNat / pow2 bit) % 2) = 1)

def getStage {XLEN : Nat} (s : State XLEN) (idx : Nat) : StageVals XLEN :=
  { ready := s.ready[idx]!
    dividend := s.dividend[idx]!
    divisor := s.divisor[idx]!
    quotient := s.quotient[idx]! }

def pushStage {XLEN : Nat} (s : State XLEN) (v : StageVals XLEN) : State XLEN :=
  { ready := s.ready.push v.ready
    dividend := s.dividend.push v.dividend
    divisor := s.divisor.push v.divisor
    quotient := s.quotient.push v.quotient }

def stageEval {XLEN : Nat} (i : Nat) (v : StageVals XLEN) : StageVals XLEN :=
  let shift := XLEN - i - 1
  let mNat := v.dividend.toNat / pow2 shift
  let nNat := v.divisor.toNat % pow2 (i + 1)
  let highNat := v.divisor.toNat / pow2 (i + 1)
  let q : Bit := if highNat = 0 then decide (nNat <= mNat) else false
  let tNat := if q then mNat - nNat else mNat
  let uNat := (v.dividend.toNat * pow2 (i + 1)) % pow2 XLEN
  let dNat := (tNat * pow2 XLEN + uNat) / pow2 (i + 1)
  let qNat := v.quotient.toNat + if q then pow2 shift else 0
  { ready := v.ready
    dividend := bv XLEN dNat
    divisor := v.divisor
    quotient := bv XLEN qNat }

def propagate {XLEN : Nat} (stageList : Bits XLEN) (prev : State XLEN) (inp : Input XLEN) : State XLEN :=
  let start : State XLEN :=
    { ready := #[inp.vld]
      dividend := #[inp.a]
      divisor := #[inp.b]
      quotient := #[bv XLEN 0] }
  let rec go (fuel idx : Nat) (acc : State XLEN) : State XLEN :=
    match fuel with
    | 0 => acc
    | fuel' + 1 =>
        let src :=
          if stageEnabled stageList (XLEN - idx - 1) then
            getStage prev idx
          else
            getStage acc idx
        let next := stageEval idx src
        go fuel' (idx + 1) (pushStage acc next)
  go XLEN 0 start

def step {XLEN : Nat} (stageList : Bits XLEN) (s : State XLEN) (i : Input XLEN) : State XLEN :=
  if i.rst then init else propagate stageList s i

def out {XLEN : Nat} (s : State XLEN) : Output XLEN :=
  { quo := s.quotient[XLEN]!
    rem := s.dividend[XLEN]!
    ack := s.ready[XLEN]! }

@[simp] theorem step_reset {XLEN : Nat} (stageList : Bits XLEN) (s : State XLEN)
    (a b : Bits XLEN) (vld : Bit) :
    step stageList s { rst := true, a := a, b := b, vld := vld } = init := by
  simp [step]

theorem step_comb_example :
    step (bv 1 0) (init (XLEN := 1))
      { rst := false, a := bv 1 1, b := bv 1 1, vld := true } =
      { ready := #[true, true]
        dividend := #[bv 1 1, bv 1 0]
        divisor := #[bv 1 1, bv 1 1]
        quotient := #[bv 1 0, bv 1 1] } := by
  native_decide

theorem out_comb_example :
    out
      (step (bv 1 0) (init (XLEN := 1))
        { rst := false, a := bv 1 1, b := bv 1 1, vld := true }) =
      { quo := bv 1 1, rem := bv 1 0, ack := true } := by
  native_decide

theorem step_reg_example :
    step (bv 1 1)
      { ready := #[true, false]
        dividend := #[bv 1 1, bv 1 0]
        divisor := #[bv 1 1, bv 1 0]
        quotient := #[bv 1 0, bv 1 0] }
      { rst := false, a := bv 1 0, b := bv 1 0, vld := false } =
      { ready := #[false, true]
        dividend := #[bv 1 0, bv 1 0]
        divisor := #[bv 1 0, bv 1 1]
        quotient := #[bv 1 0, bv 1 1] } := by
  native_decide

theorem out_reg_example :
    out
      (step (bv 1 1)
        { ready := #[true, false]
          dividend := #[bv 1 1, bv 1 0]
          divisor := #[bv 1 1, bv 1 0]
          quotient := #[bv 1 0, bv 1 0] }
        { rst := false, a := bv 1 0, b := bv 1 0, vld := false }) =
      { quo := bv 1 1, rem := bv 1 0, ack := true } := by
  native_decide

end divfunc
