import Std

namespace fpu_sp_div

abbrev Bit := Bool
abbrev Bits4 := BitVec 4
abbrev Bits6 := BitVec 6
abbrev Bits8 := BitVec 8
abbrev Bits10 := BitVec 10
abbrev Bits23 := BitVec 23
abbrev Bits24 := BitVec 24
abbrev Bits32 := BitVec 32
abbrev Bits51 := BitVec 51

structure State where
  state : Bits4
  a : Bits32
  b : Bits32
  z : Bits32
  a_m : Bits24
  b_m : Bits24
  z_m : Bits24
  a_e : Bits10
  b_e : Bits10
  z_e : Bits10
  a_s : Bit
  b_s : Bit
  z_s : Bit
  guard : Bit
  round_bit : Bit
  sticky : Bit
  quotient : Bits51
  divisor : Bits51
  dividend : Bits51
  remainder : Bits51
  count : Bits6
  result : Bits32
  rdy : Bit
deriving Repr, DecidableEq

structure Input where
  din1 : Bits32
  din2 : Bits32
  dval : Bit
deriving Repr, DecidableEq

structure Output where
  result : Bits32
  rdy : Bit
deriving Repr, DecidableEq

def bv4 (n : Nat) : Bits4 := BitVec.ofNat 4 n
def bv6 (n : Nat) : Bits6 := BitVec.ofNat 6 n
def bv8 (n : Nat) : Bits8 := BitVec.ofNat 8 n
def bv10 (n : Nat) : Bits10 := BitVec.ofNat 10 n
def bv23 (n : Nat) : Bits23 := BitVec.ofNat 23 n
def bv24 (n : Nat) : Bits24 := BitVec.ofNat 24 n
def bv32 (n : Nat) : Bits32 := BitVec.ofNat 32 n
def bv51 (n : Nat) : Bits51 := BitVec.ofNat 51 n

def WAIT_REQ : Bits4 := bv4 0
def UNPACK : Bits4 := bv4 1
def SPECIAL_CASES : Bits4 := bv4 2
def NORMALISE_A : Bits4 := bv4 3
def NORMALISE_B : Bits4 := bv4 4
def DIVIDE_0 : Bits4 := bv4 5
def DIVIDE_1 : Bits4 := bv4 6
def DIVIDE_2 : Bits4 := bv4 7
def DIVIDE_3 : Bits4 := bv4 8
def NORMALISE_1 : Bits4 := bv4 9
def NORMALISE_2 : Bits4 := bv4 10
def ROUND : Bits4 := bv4 11
def PACK : Bits4 := bv4 12
def OUT_RDY : Bits4 := bv4 13

def NEG_127 : Bits10 := bv10 897
def NEG_126 : Bits10 := bv10 898
def POS_127 : Bits10 := bv10 127
def POS_128 : Bits10 := bv10 128

def pow2 (n : Nat) : Nat := 2 ^ n

def bitVal (b : Bit) : Nat :=
  if b then 1 else 0

def testBit {w : Nat} (x : BitVec w) (i : Nat) : Bit :=
  decide (((x.toNat / pow2 i) % 2) = 1)

def slice {w len : Nat} (x : BitVec w) (lo : Nat) : BitVec len :=
  BitVec.ofNat len (x.toNat / pow2 lo)

def setBit {w : Nat} (x : BitVec w) (i : Nat) (b : Bit) : BitVec w :=
  let p := pow2 i
  let lo := x.toNat % p
  let hi := x.toNat / (p * 2)
  BitVec.ofNat w (lo + bitVal b * p + hi * p * 2)

def shl {w : Nat} (x : BitVec w) (n : Nat) : BitVec w :=
  BitVec.ofNat w (x.toNat * pow2 n)

def shr {w : Nat} (x : BitVec w) (n : Nat) : BitVec w :=
  BitVec.ofNat w (x.toNat / pow2 n)

def signedVal {w : Nat} (x : BitVec w) : Int :=
  let n := x.toNat
  if n < pow2 (w - 1) then
    Int.ofNat n
  else
    Int.ofNat n - Int.ofNat (pow2 w)

def packFloat (sgn : Bit) (exp : Bits8) (mant : Bits23) : Bits32 :=
  bv32 (bitVal sgn * pow2 31 + exp.toNat * pow2 23 + mant.toNat)

def qNaN : Bits32 :=
  packFloat true (bv8 255) (bv23 (pow2 22))

def inf32 (sgn : Bit) : Bits32 :=
  packFloat sgn (bv8 255) (bv23 0)

def zero32 (sgn : Bit) : Bits32 :=
  packFloat sgn (bv8 0) (bv23 0)

def init : State :=
  { state := WAIT_REQ
    a := bv32 0
    b := bv32 0
    z := bv32 0
    a_m := bv24 0
    b_m := bv24 0
    z_m := bv24 0
    a_e := bv10 0
    b_e := bv10 0
    z_e := bv10 0
    a_s := false
    b_s := false
    z_s := false
    guard := false
    round_bit := false
    sticky := false
    quotient := bv51 0
    divisor := bv51 0
    dividend := bv51 0
    remainder := bv51 0
    count := bv6 0
    result := bv32 0
    rdy := false }

def out (s : State) : Output :=
  { result := s.result, rdy := s.rdy }

def step (rst_n : Bit) (s : State) (i : Input) : State :=
  if rst_n = false then
    init
  else if s.state = WAIT_REQ then
    if i.dval then
      { s with rdy := false, a := i.din1, b := i.din2, state := UNPACK }
    else
      { s with rdy := false }
  else if s.state = UNPACK then
    { s with
      a_m := bv24 (slice (len := 23) s.a 0).toNat
      b_m := bv24 (slice (len := 23) s.b 0).toNat
      a_e := bv10 (slice (len := 8) s.a 23).toNat - bv10 127
      b_e := bv10 (slice (len := 8) s.b 23).toNat - bv10 127
      a_s := testBit s.a 31
      b_s := testBit s.b 31
      state := SPECIAL_CASES }
  else if s.state = SPECIAL_CASES then
    let sign := Bool.xor s.a_s s.b_s
    let aIsNaN := (s.a_e = POS_128) ∧ (s.a_m ≠ bv24 0)
    let bIsNaN := (s.b_e = POS_128) ∧ (s.b_m ≠ bv24 0)
    let aIsInf := s.a_e = POS_128
    let bIsInf := s.b_e = POS_128
    let aIsZero := (s.a_e = NEG_127) ∧ (s.a_m = bv24 0)
    let bIsZero := (s.b_e = NEG_127) ∧ (s.b_m = bv24 0)
    if aIsNaN ∨ bIsNaN then
      { s with z := qNaN, state := OUT_RDY }
    else if aIsInf ∧ bIsInf then
      { s with z := qNaN, state := OUT_RDY }
    else if aIsInf then
      let z' := if bIsZero then qNaN else inf32 sign
      { s with z := z', state := OUT_RDY }
    else if bIsInf then
      { s with z := zero32 sign, state := OUT_RDY }
    else if aIsZero then
      let z' := if bIsZero then qNaN else zero32 sign
      { s with z := z', state := OUT_RDY }
    else if bIsZero then
      { s with z := inf32 sign, state := OUT_RDY }
    else
      { s with
        a_e := if s.a_e = NEG_127 then NEG_126 else s.a_e
        b_e := if s.b_e = NEG_127 then NEG_126 else s.b_e
        a_m := if s.a_e = NEG_127 then s.a_m else setBit s.a_m 23 true
        b_m := if s.b_e = NEG_127 then s.b_m else setBit s.b_m 23 true
        state := NORMALISE_A }
  else if s.state = NORMALISE_A then
    if testBit s.a_m 23 then
      { s with state := NORMALISE_B }
    else
      { s with a_m := shl s.a_m 1, a_e := s.a_e - bv10 1 }
  else if s.state = NORMALISE_B then
    if testBit s.b_m 23 then
      { s with state := DIVIDE_0 }
    else
      { s with b_m := shl s.b_m 1, b_e := s.b_e - bv10 1 }
  else if s.state = DIVIDE_0 then
    { s with
      z_s := Bool.xor s.a_s s.b_s
      z_e := s.a_e - s.b_e
      quotient := bv51 0
      remainder := bv51 0
      count := bv6 0
      dividend := bv51 (s.a_m.toNat * pow2 27)
      divisor := bv51 s.b_m.toNat
      state := DIVIDE_1 }
  else if s.state = DIVIDE_1 then
    { s with
      quotient := shl s.quotient 1
      remainder := setBit (shl s.remainder 1) 0 (testBit s.dividend 50)
      dividend := shl s.dividend 1
      state := DIVIDE_2 }
  else if s.state = DIVIDE_2 then
    let ge := s.remainder.toNat ≥ s.divisor.toNat
    let quotient' := if ge then setBit s.quotient 0 true else s.quotient
    let remainder' := if ge then s.remainder - s.divisor else s.remainder
    if s.count = bv6 49 then
      { s with quotient := quotient', remainder := remainder', state := DIVIDE_3 }
    else
      { s with quotient := quotient', remainder := remainder', count := s.count + bv6 1, state := DIVIDE_1 }
  else if s.state = DIVIDE_3 then
    { s with
      z_m := slice (len := 24) s.quotient 3
      guard := testBit s.quotient 2
      round_bit := testBit s.quotient 1
      sticky := testBit s.quotient 0 || (s.remainder ≠ bv51 0)
      state := NORMALISE_1 }
  else if s.state = NORMALISE_1 then
    if (testBit s.z_m 23 = false) ∧ (signedVal s.z_e > -126) then
      { s with
        z_e := s.z_e - bv10 1
        z_m := setBit (shl s.z_m 1) 0 s.guard
        guard := s.round_bit
        round_bit := false }
    else
      { s with state := NORMALISE_2 }
  else if s.state = NORMALISE_2 then
    if signedVal s.z_e < -126 then
      { s with
        z_e := s.z_e + bv10 1
        z_m := shr s.z_m 1
        guard := testBit s.z_m 0
        round_bit := s.guard
        sticky := s.sticky || s.round_bit }
    else
      { s with state := ROUND }
  else if s.state = ROUND then
    if s.guard && (s.round_bit || s.sticky || testBit s.z_m 0) then
      { s with
        z_m := s.z_m + bv24 1
        z_e := if s.z_m = bv24 16777215 then s.z_e + bv10 1 else s.z_e
        state := PACK }
    else
      { s with state := PACK }
  else if s.state = PACK then
    let mant := slice (len := 23) s.z_m 0
    let exp := slice (len := 8) s.z_e 0 + bv8 127
    let z' := packFloat s.z_s exp mant
    let z' := if (signedVal s.z_e = -126) ∧ (testBit s.z_m 23 = false) then packFloat s.z_s (bv8 0) mant else z'
    let z' := if signedVal s.z_e > 127 then inf32 s.z_s else z'
    { s with z := z', state := OUT_RDY }
  else if s.state = OUT_RDY then
    { s with rdy := true, result := s.z, state := WAIT_REQ }
  else
    s

def idleInput : Input :=
  { din1 := bv32 0, din2 := bv32 0, dval := false }

@[simp] theorem step_reset (s : State) (i : Input) : step false s i = init := by
  simp [step]

theorem step_wait_req_idle :
    step true init idleInput = init := by
  native_decide

theorem step_wait_req_accept :
    step true init { din1 := bv32 7, din2 := bv32 9, dval := true } =
      { init with a := bv32 7, b := bv32 9, state := UNPACK } := by
  native_decide

theorem step_special_inf_zero_priority :
    (step true
      { init with
        state := SPECIAL_CASES
        a_e := POS_128
        b_e := NEG_127
        b_m := bv24 0
        a_s := false
        b_s := true }
      idleInput).z = qNaN := by
  native_decide

theorem step_pack_overflow :
    (step true
      { init with
        state := PACK
        z_s := true
        z_e := POS_128
        z_m := bv24 0 }
      idleInput).z = inf32 true := by
  native_decide

theorem step_out_rdy :
    step true { init with state := OUT_RDY, z := bv32 123 } idleInput =
      { init with state := WAIT_REQ, z := bv32 123, result := bv32 123, rdy := true } := by
  native_decide

end fpu_sp_div
