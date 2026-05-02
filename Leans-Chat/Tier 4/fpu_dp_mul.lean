import Std

namespace fpu_dp_mul

abbrev Bit := Bool
abbrev Bits11 := BitVec 11
abbrev Bits13 := BitVec 13
abbrev Bits52 := BitVec 52
abbrev Bits53 := BitVec 53
abbrev Bits64 := BitVec 64
abbrev Bits106 := BitVec 106

def pow2 (n : Nat) : Nat := 2 ^ n

def bitToNat (b : Bit) : Nat := if b then 1 else 0

def bv11 (n : Nat) : Bits11 := BitVec.ofNat 11 n
def bv13 (n : Nat) : Bits13 := BitVec.ofNat 13 n
def bv52 (n : Nat) : Bits52 := BitVec.ofNat 52 n
def bv53 (n : Nat) : Bits53 := BitVec.ofNat 53 n
def bv64 (n : Nat) : Bits64 := BitVec.ofNat 64 n
def bv106 (n : Nat) : Bits106 := BitVec.ofNat 106 n

def sliceNat {n : Nat} (x : BitVec n) (lo width : Nat) : Nat :=
  (x.toNat / pow2 lo) % pow2 width

def getBit {n : Nat} (x : BitVec n) (idx : Nat) : Bit :=
  sliceNat x idx 1 = 1

def shl {n : Nat} (x : BitVec n) (k : Nat) : BitVec n :=
  BitVec.ofNat n (x.toNat * pow2 k)

def shr {n : Nat} (x : BitVec n) (k : Nat) : BitVec n :=
  BitVec.ofNat n (x.toNat / pow2 k)

def setBit {n : Nat} (x : BitVec n) (idx : Nat) (b : Bit) : BitVec n :=
  let lower := sliceNat x 0 idx
  let upper := x.toNat / pow2 (idx + 1)
  BitVec.ofNat n (lower + bitToNat b * pow2 idx + upper * pow2 (idx + 1))

def addBV {n : Nat} (x y : BitVec n) : BitVec n :=
  BitVec.ofNat n (x.toNat + y.toNat)

def subBV {n : Nat} (x y : BitVec n) : BitVec n :=
  BitVec.ofNat n (x.toNat + pow2 n - y.toNat)

def bxor (a b : Bit) : Bit :=
  (a && !b) || (!a && b)

def signed13 (x : Bits13) : Int :=
  if x.toNat < pow2 12 then
    Int.ofNat x.toNat
  else
    Int.ofNat x.toNat - Int.ofNat (pow2 13)

def low52 (x : Bits53) : Bits52 :=
  bv52 (sliceNat x 0 52)

def expField (x : Bits13) : Bits11 :=
  bv11 (sliceNat x 0 12 + 1023)

def mkFloat (sign : Bit) (exp : Bits11) (mant : Bits52) : Bits64 :=
  bv64 (bitToNat sign * pow2 63 + exp.toNat * pow2 52 + mant.toNat)

def canonicalNaN : Bits64 :=
  mkFloat true (bv11 2047) (bv52 (pow2 51))

def infOf (sign : Bit) : Bits64 :=
  mkFloat sign (bv11 2047) (bv52 0)

def zeroOf (sign : Bit) : Bits64 :=
  mkFloat sign (bv11 0) (bv52 0)

def isNaNUnpacked (e : Bits13) (m : Bits53) : Prop :=
  e = bv13 1024 ∧ m.toNat ≠ 0

def isZeroUnpacked (e : Bits13) (m : Bits53) : Prop :=
  signed13 e = -1023 ∧ m.toNat = 0

inductive Phase where
  | WAIT_REQ
  | UNPACK
  | SPECIAL_CASES
  | NORMALISE_A
  | NORMALISE_B
  | MULTIPLY_0
  | MULTIPLY_1
  | NORMALISE_1
  | NORMALISE_2
  | ROUND
  | PACK
  | OUT_RDY
deriving Repr, DecidableEq

structure State where
  phase : Phase
  a : Bits64
  b : Bits64
  z : Bits64
  result : Bits64
  a_m : Bits53
  b_m : Bits53
  z_m : Bits53
  a_e : Bits13
  b_e : Bits13
  z_e : Bits13
  a_s : Bit
  b_s : Bit
  z_s : Bit
  guard : Bit
  round_bit : Bit
  sticky : Bit
  product : Bits106
  rdy : Bit
deriving Repr, DecidableEq

structure Input where
  din1 : Bits64
  din2 : Bits64
  dval : Bit
deriving Repr, DecidableEq

structure Output where
  result : Bits64
  rdy : Bit
deriving Repr, DecidableEq

def init : State :=
  { phase := Phase.WAIT_REQ
    a := bv64 0
    b := bv64 0
    z := bv64 0
    result := bv64 0
    a_m := bv53 0
    b_m := bv53 0
    z_m := bv53 0
    a_e := bv13 0
    b_e := bv13 0
    z_e := bv13 0
    a_s := false
    b_s := false
    z_s := false
    guard := false
    round_bit := false
    sticky := false
    product := bv106 0
    rdy := false }

def step (s : State) (rst_n : Bit) (i : Input) : State :=
  if rst_n then
    match s.phase with
    | .WAIT_REQ =>
        if i.dval then
          { s with rdy := false, a := i.din1, b := i.din2, phase := .UNPACK }
        else
          { s with rdy := false }
    | .UNPACK =>
        { s with
          a_m := bv53 (sliceNat s.a 0 52)
          b_m := bv53 (sliceNat s.b 0 52)
          a_e := subBV (bv13 (sliceNat s.a 52 11)) (bv13 1023)
          b_e := subBV (bv13 (sliceNat s.b 52 11)) (bv13 1023)
          a_s := getBit s.a 63
          b_s := getBit s.b 63
          phase := .SPECIAL_CASES }
    | .SPECIAL_CASES =>
        if isNaNUnpacked s.a_e s.a_m ∨ isNaNUnpacked s.b_e s.b_m then
          { s with z := canonicalNaN, phase := .OUT_RDY }
        else if s.a_e = bv13 1024 then
          if isZeroUnpacked s.b_e s.b_m then
            { s with z := canonicalNaN, phase := .OUT_RDY }
          else
            { s with z := infOf (bxor s.a_s s.b_s), phase := .OUT_RDY }
        else if s.b_e = bv13 1024 then
          if isZeroUnpacked s.a_e s.a_m then
            { s with z := canonicalNaN, phase := .OUT_RDY }
          else
            { s with z := infOf (bxor s.a_s s.b_s), phase := .OUT_RDY }
        else if isZeroUnpacked s.a_e s.a_m then
          { s with z := zeroOf (bxor s.a_s s.b_s), phase := .OUT_RDY }
        else if isZeroUnpacked s.b_e s.b_m then
          { s with z := zeroOf (bxor s.a_s s.b_s), phase := .OUT_RDY }
        else
          let a_e' := if signed13 s.a_e = -1023 then bv13 7170 else s.a_e
          let b_e' := if signed13 s.b_e = -1023 then bv13 7170 else s.b_e
          let a_m' := if signed13 s.a_e = -1023 then s.a_m else setBit s.a_m 52 true
          let b_m' := if signed13 s.b_e = -1023 then s.b_m else setBit s.b_m 52 true
          { s with a_e := a_e', b_e := b_e', a_m := a_m', b_m := b_m', phase := .NORMALISE_A }
    | .NORMALISE_A =>
        if getBit s.a_m 52 then
          { s with phase := .NORMALISE_B }
        else
          { s with a_m := shl s.a_m 1, a_e := subBV s.a_e (bv13 1) }
    | .NORMALISE_B =>
        if getBit s.b_m 52 then
          { s with phase := .MULTIPLY_0 }
        else
          { s with b_m := shl s.b_m 1, b_e := subBV s.b_e (bv13 1) }
    | .MULTIPLY_0 =>
        { s with
          z_s := bxor s.a_s s.b_s
          z_e := addBV (addBV s.a_e s.b_e) (bv13 1)
          product := bv106 (s.a_m.toNat * s.b_m.toNat)
          phase := .MULTIPLY_1 }
    | .MULTIPLY_1 =>
        { s with
          z_m := bv53 (sliceNat s.product 53 53)
          guard := getBit s.product 52
          round_bit := getBit s.product 51
          sticky := sliceNat s.product 0 51 ≠ 0
          phase := .NORMALISE_1 }
    | .NORMALISE_1 =>
        if getBit s.z_m 52 then
          { s with phase := .NORMALISE_2 }
        else
          { s with
            z_e := subBV s.z_e (bv13 1)
            z_m := setBit (shl s.z_m 1) 0 s.guard
            guard := s.round_bit
            round_bit := false }
    | .NORMALISE_2 =>
        if signed13 s.z_e < -1022 then
          { s with
            z_e := addBV s.z_e (bv13 1)
            z_m := shr s.z_m 1
            guard := getBit s.z_m 0
            round_bit := s.guard
            sticky := s.sticky || s.round_bit }
        else
          { s with phase := .ROUND }
    | .ROUND =>
        if s.guard && (s.round_bit || s.sticky || getBit s.z_m 0) then
          let z_e' := if s.z_m = bv53 (pow2 53 - 1) then addBV s.z_e (bv13 1) else s.z_e
          { s with z_m := addBV s.z_m (bv53 1), z_e := z_e', phase := .PACK }
        else
          { s with phase := .PACK }
    | .PACK =>
        let base := mkFloat s.z_s (expField s.z_e) (low52 s.z_m)
        let subnorm :=
          if signed13 s.z_e = -1022 ∧ !(getBit s.z_m 52) then
            mkFloat s.z_s (bv11 0) (low52 s.z_m)
          else
            base
        let finalZ :=
          if signed13 s.z_e > 1023 then
            infOf s.z_s
          else
            subnorm
        { s with z := finalZ, phase := .OUT_RDY }
    | .OUT_RDY =>
        { s with rdy := true, result := s.z, phase := .WAIT_REQ }
  else
    { s with phase := .WAIT_REQ, rdy := false }

def out (s : State) : Output :=
  { result := s.result, rdy := s.rdy }

def zeroInput : Input :=
  { din1 := bv64 0, din2 := bv64 0, dval := false }

@[simp] theorem step_reset (i : Input) :
    step init false i = { init with phase := Phase.WAIT_REQ, rdy := false } := by
  native_decide

@[simp] theorem step_wait_req_hold :
    step init true zeroInput = { init with rdy := false } := by
  native_decide

@[simp] theorem step_wait_req_start :
    step init true { din1 := bv64 7, din2 := bv64 9, dval := true } =
      { init with rdy := false, a := bv64 7, b := bv64 9, phase := Phase.UNPACK } := by
  native_decide

def sUnpackZero : State :=
  { init with phase := Phase.UNPACK }

theorem step_unpack_zero :
    step sUnpackZero true zeroInput =
      { sUnpackZero with
        a_m := bv53 0
        b_m := bv53 0
        a_e := bv13 7169
        b_e := bv13 7169
        a_s := false
        b_s := false
        phase := Phase.SPECIAL_CASES } := by
  native_decide

def sSpecialNaN : State :=
  { init with phase := Phase.SPECIAL_CASES, a_e := bv13 1024, a_m := bv53 1 }

theorem step_special_nan :
    step sSpecialNaN true zeroInput =
      { sSpecialNaN with z := canonicalNaN, phase := Phase.OUT_RDY } := by
  native_decide

def sNormaliseAShift : State :=
  { init with phase := Phase.NORMALISE_A, a_m := bv53 1, a_e := bv13 5 }

theorem step_normalise_a_shift :
    step sNormaliseAShift true zeroInput =
      { sNormaliseAShift with a_m := bv53 2, a_e := bv13 4 } := by
  native_decide

def sNormaliseBDone : State :=
  { init with phase := Phase.NORMALISE_B, b_m := bv53 (pow2 52) }

theorem step_normalise_b_done :
    step sNormaliseBDone true zeroInput =
      { sNormaliseBDone with phase := Phase.MULTIPLY_0 } := by
  native_decide

def sMultiply0 : State :=
  { init with
    phase := Phase.MULTIPLY_0
    a_s := true
    b_s := false
    a_e := bv13 2
    b_e := bv13 3
    a_m := bv53 3
    b_m := bv53 4 }

theorem step_multiply_0 :
    step sMultiply0 true zeroInput =
      { sMultiply0 with
        z_s := true
        z_e := bv13 6
        product := bv106 12
        phase := Phase.MULTIPLY_1 } := by
  native_decide

def sMultiply1 : State :=
  { init with phase := Phase.MULTIPLY_1, product := bv106 (pow2 53) }

theorem step_multiply_1 :
    step sMultiply1 true zeroInput =
      { sMultiply1 with
        z_m := bv53 1
        guard := false
        round_bit := false
        sticky := false
        phase := Phase.NORMALISE_1 } := by
  native_decide

def sNormalise1Shift : State :=
  { init with
    phase := Phase.NORMALISE_1
    z_m := bv53 1
    z_e := bv13 5
    guard := true
    round_bit := true }

theorem step_normalise_1_shift :
    step sNormalise1Shift true zeroInput =
      { sNormalise1Shift with
        z_e := bv13 4
        z_m := bv53 3
        guard := true
        round_bit := false } := by
  native_decide

def sNormalise2Shift : State :=
  { init with
    phase := Phase.NORMALISE_2
    z_m := bv53 3
    z_e := bv13 7169
    guard := true
    round_bit := false
    sticky := false }

theorem step_normalise_2_shift :
    step sNormalise2Shift true zeroInput =
      { sNormalise2Shift with
        z_e := bv13 7170
        z_m := bv53 1
        guard := true
        round_bit := true
        sticky := false } := by
  native_decide

def sRoundCarry : State :=
  { init with
    phase := Phase.ROUND
    z_m := bv53 (pow2 53 - 1)
    z_e := bv13 5
    guard := true
    round_bit := false
    sticky := false }

theorem step_round_carry :
    step sRoundCarry true zeroInput =
      { sRoundCarry with
        z_m := bv53 0
        z_e := bv13 6
        phase := Phase.PACK } := by
  native_decide

def sPackNormal : State :=
  { init with phase := Phase.PACK, z_s := false, z_e := bv13 0, z_m := bv53 (pow2 52) }

theorem step_pack_normal :
    step sPackNormal true zeroInput =
      { sPackNormal with z := mkFloat false (bv11 1023) (bv52 0), phase := Phase.OUT_RDY } := by
  native_decide

def sPackOverflow : State :=
  { init with phase := Phase.PACK, z_s := true, z_e := bv13 1024, z_m := bv53 0 }

theorem step_pack_overflow :
    step sPackOverflow true zeroInput =
      { sPackOverflow with z := infOf true, phase := Phase.OUT_RDY } := by
  native_decide

def sOutRdy : State :=
  { init with phase := Phase.OUT_RDY, z := bv64 17 }

@[simp] theorem step_out_rdy :
    step sOutRdy true zeroInput =
      { sOutRdy with rdy := true, result := bv64 17, phase := Phase.WAIT_REQ } := by
  native_decide

@[simp] theorem step_reset_priority :
    step sOutRdy false zeroInput =
      { sOutRdy with phase := Phase.WAIT_REQ, rdy := false } := by
  native_decide

end fpu_dp_mul
