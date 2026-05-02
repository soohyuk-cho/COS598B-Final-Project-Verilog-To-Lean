import Std

namespace fpu_dp_div

abbrev Bit := Bool
abbrev Bits4 := BitVec 4
abbrev Bits7 := BitVec 7
abbrev Bits11 := BitVec 11
abbrev Bits52 := BitVec 52
abbrev Bits53 := BitVec 53
abbrev Bits64 := BitVec 64
abbrev Bits109 := BitVec 109

def bv (n : Nat) (x : Nat) : BitVec n := BitVec.ofNat n x

def pow2 (n : Nat) : Nat := 2 ^ n

def intModPow2 (n : Nat) (x : Int) : Nat :=
  Int.toNat (x % Int.ofNat (pow2 n))

def intToBv (n : Nat) (x : Int) : BitVec n :=
  bv n (intModPow2 n x)

def bitVal (b : Bit) : Nat :=
  if b then 1 else 0

def getBit {n : Nat} (x : BitVec n) (i : Nat) : Bit :=
  ((x.toNat / pow2 i) % 2) = 1

def extract {n : Nat} (m lo : Nat) (x : BitVec n) : BitVec m :=
  bv m ((x.toNat / pow2 lo) % pow2 m)

def setBit {n : Nat} (x : BitVec n) (i : Nat) (b : Bit) : BitVec n :=
  let old := bitVal (getBit x i)
  bv n (x.toNat - old * pow2 i + bitVal b * pow2 i)

def setField {n m : Nat} (x : BitVec n) (lo : Nat) (y : BitVec m) : BitVec n :=
  let lower := x.toNat % pow2 lo
  let upper := x.toNat / pow2 (lo + m)
  bv n (lower + y.toNat * pow2 lo + upper * pow2 (lo + m))

def shl {n : Nat} (x : BitVec n) (k : Nat) : BitVec n :=
  bv n (x.toNat * pow2 k)

def lshr {n : Nat} (x : BitVec n) (k : Nat) : BitVec n :=
  bv n (x.toNat / pow2 k)

def bvAdd {n : Nat} (x y : BitVec n) : BitVec n :=
  bv n (x.toNat + y.toNat)

def bvAddNat {n : Nat} (x : BitVec n) (k : Nat) : BitVec n :=
  bv n (x.toNat + k)

def bvSub {n : Nat} (x y : BitVec n) : BitVec n :=
  bv n (x.toNat + pow2 n - y.toNat)

def bxor (a b : Bit) : Bit :=
  (a && !b) || (!a && b)

def packWord (sign : Bit) (exp : Bits11) (frac : Bits52) : Bits64 :=
  let z0 := bv 64 0
  let z1 := setField z0 0 frac
  let z2 := setField z1 52 exp
  setBit z2 63 sign

def canonicalNaN : Bits64 :=
  packWord true (bv 11 2047) (setBit (bv 52 0) 51 true)

def infinityWord (sign : Bit) : Bits64 :=
  packWord sign (bv 11 2047) (bv 52 0)

def zeroWord (sign : Bit) : Bits64 :=
  packWord sign (bv 11 0) (bv 52 0)

def WAIT_REQ : Bits4 := bv 4 0
def UNPACK : Bits4 := bv 4 1
def SPECIAL_CASES : Bits4 := bv 4 2
def NORMALISE_A : Bits4 := bv 4 3
def NORMALISE_B : Bits4 := bv 4 4
def DIVIDE_0 : Bits4 := bv 4 5
def DIVIDE_1 : Bits4 := bv 4 6
def DIVIDE_2 : Bits4 := bv 4 7
def DIVIDE_3 : Bits4 := bv 4 8
def NORMALISE_1 : Bits4 := bv 4 9
def NORMALISE_2 : Bits4 := bv 4 10
def ROUND : Bits4 := bv 4 11
def PACK : Bits4 := bv 4 12
def OUT_RDY : Bits4 := bv 4 13

def isNaNVal (e : Int) (m : Bits53) : Prop :=
  e = 1024 ∧ m.toNat ≠ 0

def isZeroVal (e : Int) (m : Bits53) : Prop :=
  e = -1023 ∧ m.toNat = 0

structure State where
  state : Bits4
  a : Bits64
  b : Bits64
  z : Bits64
  a_m : Bits53
  b_m : Bits53
  z_m : Bits53
  a_e : Int
  b_e : Int
  z_e : Int
  a_s : Bit
  b_s : Bit
  z_s : Bit
  guard : Bit
  round_bit : Bit
  sticky : Bit
  quotient : Bits109
  divisor : Bits109
  dividend : Bits109
  remainder : Bits109
  count : Bits7
  result : Bits64
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
  { state := WAIT_REQ
    a := bv 64 0
    b := bv 64 0
    z := bv 64 0
    a_m := bv 53 0
    b_m := bv 53 0
    z_m := bv 53 0
    a_e := 0
    b_e := 0
    z_e := 0
    a_s := false
    b_s := false
    z_s := false
    guard := false
    round_bit := false
    sticky := false
    quotient := bv 109 0
    divisor := bv 109 0
    dividend := bv 109 0
    remainder := bv 109 0
    count := bv 7 0
    result := bv 64 0
    rdy := false }

def step (rst_n : Bit) (s : State) (i : Input) : State :=
  match rst_n with
  | false =>
      { s with state := WAIT_REQ, rdy := false }
  | true =>
      match s.state.toNat with
      | 0 =>
          let s1 := { s with rdy := false }
          match i.dval with
          | true => { s1 with a := i.din1, b := i.din2, state := UNPACK }
          | false => s1
      | 1 =>
          { s with
            a_m := bv 53 (extract 52 0 s.a).toNat
            b_m := bv 53 (extract 52 0 s.b).toNat
            a_e := Int.ofNat (extract 11 52 s.a).toNat - 1023
            b_e := Int.ofNat (extract 11 52 s.b).toNat - 1023
            a_s := getBit s.a 63
            b_s := getBit s.b 63
            state := SPECIAL_CASES }
      | 2 =>
          let sign := bxor s.a_s s.b_s
          if hNaN : isNaNVal s.a_e s.a_m ∨ isNaNVal s.b_e s.b_m then
            { s with z := canonicalNaN, state := OUT_RDY }
          else if hInfInf : s.a_e = 1024 ∧ s.b_e = 1024 then
            { s with z := canonicalNaN, state := OUT_RDY }
          else if hAInf : s.a_e = 1024 then
            let s1 := { s with z := infinityWord sign, state := OUT_RDY }
            if hBZero : isZeroVal s.b_e s.b_m then
              { s1 with z := canonicalNaN, state := OUT_RDY }
            else
              s1
          else if hBInf : s.b_e = 1024 then
            { s with z := zeroWord sign, state := OUT_RDY }
          else if hAZero : isZeroVal s.a_e s.a_m then
            let s1 := { s with z := zeroWord sign, state := OUT_RDY }
            if hBZero : isZeroVal s.b_e s.b_m then
              { s1 with z := canonicalNaN, state := OUT_RDY }
            else
              s1
          else if hBZero : isZeroVal s.b_e s.b_m then
            { s with z := infinityWord sign, state := OUT_RDY }
          else
            let s1 :=
              if hADenorm : s.a_e = -1023 then
                { s with a_e := -1022 }
              else
                { s with a_m := setBit s.a_m 52 true }
            let s2 :=
              if hBDenorm : s.b_e = -1023 then
                { s1 with b_e := -1022 }
              else
                { s1 with b_m := setBit s.b_m 52 true }
            { s2 with state := NORMALISE_A }
      | 3 =>
          match getBit s.a_m 52 with
          | true => { s with state := NORMALISE_B }
          | false => { s with a_m := shl s.a_m 1, a_e := s.a_e - 1 }
      | 4 =>
          match getBit s.b_m 52 with
          | true => { s with state := DIVIDE_0 }
          | false => { s with b_m := shl s.b_m 1, b_e := s.b_e - 1 }
      | 5 =>
          { s with
            z_s := bxor s.a_s s.b_s
            z_e := s.a_e - s.b_e
            quotient := bv 109 0
            remainder := bv 109 0
            count := bv 7 0
            dividend := bv 109 (s.a_m.toNat * pow2 56)
            divisor := bv 109 s.b_m.toNat
            state := DIVIDE_1 }
      | 6 =>
          let rem1 := setBit (shl s.remainder 1) 0 (getBit s.dividend 108)
          { s with
            quotient := shl s.quotient 1
            remainder := rem1
            dividend := shl s.dividend 1
            state := DIVIDE_2 }
      | 7 =>
          let s1 :=
            if hGe : s.remainder.toNat >= s.divisor.toNat then
              { s with quotient := setBit s.quotient 0 true, remainder := bvSub s.remainder s.divisor }
            else
              s
          if hCount : s.count.toNat = 107 then
            { s1 with state := DIVIDE_3 }
          else
            { s1 with count := bvAddNat s.count 1, state := DIVIDE_1 }
      | 8 =>
          { s with
            z_m := extract 53 3 s.quotient
            guard := getBit s.quotient 2
            round_bit := getBit s.quotient 1
            sticky := getBit s.quotient 0 || decide (s.remainder.toNat ≠ 0)
            state := NORMALISE_1 }
      | 9 =>
          if hNorm : getBit s.z_m 52 = false ∧ s.z_e > -1022 then
            { s with
              z_e := s.z_e - 1
              z_m := setBit (shl s.z_m 1) 0 s.guard
              guard := s.round_bit
              round_bit := false }
          else
            { s with state := NORMALISE_2 }
      | 10 =>
          if hSub : s.z_e < -1022 then
            { s with
              z_e := s.z_e + 1
              z_m := lshr s.z_m 1
              guard := getBit s.z_m 0
              round_bit := s.guard
              sticky := s.sticky || s.round_bit }
          else
            { s with state := ROUND }
      | 11 =>
          let roundUp := s.guard && (s.round_bit || s.sticky || getBit s.z_m 0)
          match roundUp with
          | true =>
              let s1 := { s with z_m := bvAddNat s.z_m 1 }
              let s2 :=
                if hCarry : s.z_m.toNat = 0xffffff then
                  { s1 with z_e := s.z_e + 1 }
                else
                  s1
              { s2 with state := PACK }
          | false =>
              { s with state := PACK }
      | 12 =>
          let z1 := setField s.z 0 (extract 52 0 s.z_m)
          let z2 := setField z1 52 (bvAddNat (intToBv 11 s.z_e) 1023)
          let z3 := setBit z2 63 s.z_s
          let z4 :=
            if hTiny : s.z_e = -1022 ∧ getBit s.z_m 52 = false then
              setField z3 52 (bv 11 0)
            else
              z3
          let z5 :=
            if hOverflow : s.z_e > 1023 then
              setBit (setField (setField z4 0 (bv 52 0)) 52 (bv 11 2047)) 63 s.z_s
            else
              z4
          { s with z := z5, state := OUT_RDY }
      | 13 =>
          { s with rdy := true, result := s.z, state := WAIT_REQ }
      | _ =>
          s

def out (s : State) : Output :=
  { result := s.result, rdy := s.rdy }

@[simp] theorem step_reset (s : State) (i : Input) :
    step false s i = { s with state := WAIT_REQ, rdy := false } := by
  rfl

def blankInput : Input :=
  { din1 := bv 64 0, din2 := bv 64 0, dval := false }

def acceptInput : Input :=
  { din1 := bv 64 7, din2 := bv 64 9, dval := true }

@[simp] theorem step_wait_req_idle :
    step true init blankInput = { init with rdy := false } := by
  native_decide

@[simp] theorem step_wait_req_accept :
    step true init acceptInput =
      { init with a := bv 64 7, b := bv 64 9, state := UNPACK } := by
  native_decide

def specialNanState : State :=
  { init with
    state := SPECIAL_CASES
    a_e := 1024
    a_m := bv 53 1
    b_e := 1024
    b_m := bv 53 0 }

@[simp] theorem step_special_nan_priority :
    step true specialNanState blankInput =
      { specialNanState with z := canonicalNaN, state := OUT_RDY } := by
  native_decide

def outReadyState : State :=
  { init with state := OUT_RDY, z := bv 64 42 }

@[simp] theorem step_out_rdy :
    step true outReadyState blankInput =
      { outReadyState with rdy := true, result := bv 64 42, state := WAIT_REQ } := by
  native_decide

@[simp] theorem out_init :
    out init = { result := bv 64 0, rdy := false } := by
  rfl

end fpu_dp_div
