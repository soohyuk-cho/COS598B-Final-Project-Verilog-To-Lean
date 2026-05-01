import Std

namespace fpu_sp_mul

abbrev Bit := Bool
abbrev Bits4 := BitVec 4
abbrev Bits8 := BitVec 8
abbrev Bits10 := BitVec 10
abbrev Bits23 := BitVec 23
abbrev Bits24 := BitVec 24
abbrev Bits32 := BitVec 32
abbrev Bits48 := BitVec 48

def bv4 (n : Nat) : Bits4 := BitVec.ofNat 4 n
def bv8 (n : Nat) : Bits8 := BitVec.ofNat 8 n
def bv10 (n : Nat) : Bits10 := BitVec.ofNat 10 n
def bv23 (n : Nat) : Bits23 := BitVec.ofNat 23 n
def bv24 (n : Nat) : Bits24 := BitVec.ofNat 24 n
def bv32 (n : Nat) : Bits32 := BitVec.ofNat 32 n
def bv48 (n : Nat) : Bits48 := BitVec.ofNat 48 n

def b2n (b : Bit) : Nat :=
  if b then 1 else 0

def bxor (a b : Bit) : Bit :=
  match a, b with
  | true, false => true
  | false, true => true
  | _, _ => false

def bit {w : Nat} (x : BitVec w) (i : Nat) : Bit :=
  Nat.testBit x.toNat i

def shl {w : Nat} (x : BitVec w) (n : Nat) : BitVec w :=
  BitVec.ofNat w (x.toNat * (2 ^ n))

def lshr {w : Nat} (x : BitVec w) (n : Nat) : BitVec w :=
  BitVec.ofNat w (x.toNat / (2 ^ n))

def add {w : Nat} (x y : BitVec w) : BitVec w :=
  BitVec.ofNat w (x.toNat + y.toNat)

def sub {w : Nat} (x y : BitVec w) : BitVec w :=
  BitVec.ofNat w (x.toNat + (2 ^ w) - y.toNat)

def withBit {w : Nat} (x : BitVec w) (i : Nat) (b : Bit) : BitVec w :=
  let n := x.toNat
  let cleared := if Nat.testBit n i then n - (2 ^ i) else n
  let updated := if b then cleared + (2 ^ i) else cleared
  BitVec.ofNat w updated

def fracOf32 (x : Bits32) : Bits23 :=
  bv23 x.toNat

def expOf32 (x : Bits32) : Bits8 :=
  bv8 (x.toNat / (2 ^ 23))

def signOf32 (x : Bits32) : Bit :=
  bit x 31

def top24Of48 (x : Bits48) : Bits24 :=
  bv24 (x.toNat / (2 ^ 24))

def low22Nonzero48 (x : Bits48) : Bit :=
  decide ((x.toNat % (2 ^ 22)) ≠ 0)

def fracOf24 (x : Bits24) : Bits23 :=
  bv23 x.toNat

def low8Of10 (x : Bits10) : Bits8 :=
  bv8 x.toNat

def signed10 (x : Bits10) : Int :=
  if bit x 9 then
    Int.ofNat x.toNat - Int.ofNat (2 ^ 10)
  else
    Int.ofNat x.toNat

def mkFloat (sign : Bit) (exp : Bits8) (frac : Bits23) : Bits32 :=
  bv32 (b2n sign * (2 ^ 31) + exp.toNat * (2 ^ 23) + frac.toNat)

def nan32 : Bits32 :=
  mkFloat true (bv8 255) (bv23 (2 ^ 22))

def inf32 (sign : Bit) : Bits32 :=
  mkFloat sign (bv8 255) (bv23 0)

def zero32 (sign : Bit) : Bits32 :=
  mkFloat sign (bv8 0) (bv23 0)

def WAIT_REQ : Bits4 := bv4 0
def UNPACK : Bits4 := bv4 1
def SPECIAL_CASES : Bits4 := bv4 2
def NORMALISE_A : Bits4 := bv4 3
def NORMALISE_B : Bits4 := bv4 4
def MULTIPLY_0 : Bits4 := bv4 5
def MULTIPLY_1 : Bits4 := bv4 6
def NORMALISE_1 : Bits4 := bv4 7
def NORMALISE_2 : Bits4 := bv4 8
def ROUND : Bits4 := bv4 9
def PACK : Bits4 := bv4 10
def OUT_RDY : Bits4 := bv4 11

structure State where
  s_output_z_stb : Bit
  s_output_z : Bits32
  s_input_a_ack : Bit
  s_input_b_ack : Bit
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
  product : Bits48
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

def init : State := {
  s_output_z_stb := false
  s_output_z := bv32 0
  s_input_a_ack := false
  s_input_b_ack := false
  state := WAIT_REQ
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
  product := bv48 0
  result := bv32 0
  rdy := false
}

def step (rst_n : Bit) (s : State) (i : Input) : State :=
  if rst_n = false then
    { s with state := WAIT_REQ, rdy := false }
  else if s.state = WAIT_REQ then
    if i.dval then
      { s with rdy := false, a := i.din1, b := i.din2, state := UNPACK }
    else
      { s with rdy := false }
  else if s.state = UNPACK then
    { s with
      a_m := bv24 (fracOf32 s.a).toNat
      b_m := bv24 (fracOf32 s.b).toNat
      a_e := sub (bv10 (expOf32 s.a).toNat) (bv10 127)
      b_e := sub (bv10 (expOf32 s.b).toNat) (bv10 127)
      a_s := signOf32 s.a
      b_s := signOf32 s.b
      state := SPECIAL_CASES }
  else if s.state = SPECIAL_CASES then
    if ((s.a_e = bv10 128 ∧ s.a_m ≠ bv24 0) ∨ (s.b_e = bv10 128 ∧ s.b_m ≠ bv24 0)) then
      { s with z := nan32, state := OUT_RDY }
    else if s.a_e = bv10 128 then
      let z0 := inf32 (bxor s.a_s s.b_s)
      let z1 := if signed10 s.b_e = -127 ∧ s.b_m = bv24 0 then nan32 else z0
      { s with z := z1, state := OUT_RDY }
    else if s.b_e = bv10 128 then
      let z0 := inf32 (bxor s.a_s s.b_s)
      let z1 := if signed10 s.a_e = -127 ∧ s.a_m = bv24 0 then nan32 else z0
      { s with z := z1, state := OUT_RDY }
    else if signed10 s.a_e = -127 ∧ s.a_m = bv24 0 then
      { s with z := zero32 (bxor s.a_s s.b_s), state := OUT_RDY }
    else if signed10 s.b_e = -127 ∧ s.b_m = bv24 0 then
      { s with z := zero32 (bxor s.a_s s.b_s), state := OUT_RDY }
    else
      let a_e' := if signed10 s.a_e = -127 then bv10 898 else s.a_e
      let a_m' := if signed10 s.a_e = -127 then s.a_m else withBit s.a_m 23 true
      let b_e' := if signed10 s.b_e = -127 then bv10 898 else s.b_e
      let b_m' := if signed10 s.b_e = -127 then s.b_m else withBit s.b_m 23 true
      { s with a_e := a_e', a_m := a_m', b_e := b_e', b_m := b_m', state := NORMALISE_A }
  else if s.state = NORMALISE_A then
    if bit s.a_m 23 then
      { s with state := NORMALISE_B }
    else
      { s with a_m := shl s.a_m 1, a_e := sub s.a_e (bv10 1) }
  else if s.state = NORMALISE_B then
    if bit s.b_m 23 then
      { s with state := MULTIPLY_0 }
    else
      { s with b_m := shl s.b_m 1, b_e := sub s.b_e (bv10 1) }
  else if s.state = MULTIPLY_0 then
    { s with
      z_s := bxor s.a_s s.b_s
      z_e := add (add s.a_e s.b_e) (bv10 1)
      product := bv48 (s.a_m.toNat * s.b_m.toNat)
      state := MULTIPLY_1 }
  else if s.state = MULTIPLY_1 then
    { s with
      z_m := top24Of48 s.product
      guard := bit s.product 23
      round_bit := bit s.product 22
      sticky := low22Nonzero48 s.product
      state := NORMALISE_1 }
  else if s.state = NORMALISE_1 then
    if bit s.z_m 23 = false then
      let shifted := shl s.z_m 1
      let z_m' := withBit shifted 0 s.guard
      { s with
        z_e := sub s.z_e (bv10 1)
        z_m := z_m'
        guard := s.round_bit
        round_bit := false }
    else
      { s with state := NORMALISE_2 }
  else if s.state = NORMALISE_2 then
    if signed10 s.z_e < -126 then
      { s with
        z_e := add s.z_e (bv10 1)
        z_m := lshr s.z_m 1
        guard := bit s.z_m 0
        round_bit := s.guard
        sticky := s.sticky || s.round_bit }
    else
      { s with state := ROUND }
  else if s.state = ROUND then
    if s.guard && (s.round_bit || s.sticky || bit s.z_m 0) then
      let z_e' := if s.z_m = bv24 16777215 then add s.z_e (bv10 1) else s.z_e
      { s with z_m := add s.z_m (bv24 1), z_e := z_e', state := PACK }
    else
      { s with state := PACK }
  else if s.state = PACK then
    let frac := fracOf24 s.z_m
    let exp := bv8 (low8Of10 s.z_e).toNat.succ.pred
    let expBiased := bv8 (exp.toNat + 127)
    let z0 := mkFloat s.z_s expBiased frac
    let z1 := if signed10 s.z_e = -126 ∧ bit s.z_m 23 = false then mkFloat s.z_s (bv8 0) frac else z0
    let z2 := if signed10 s.z_e > 127 then inf32 s.z_s else z1
    { s with z := z2, state := OUT_RDY }
  else if s.state = OUT_RDY then
    { s with rdy := true, result := s.z, state := WAIT_REQ }
  else
    s

def out (s : State) : Output := {
  result := s.result
  rdy := s.rdy
}

def zeroInput : Input := {
  din1 := bv32 0
  din2 := bv32 0
  dval := false
}

def one32 : Bits32 := bv32 1065353216

@[simp] theorem step_reset (s : State) (i : Input) :
    step false s i = { s with state := WAIT_REQ, rdy := false } := by
  simp [step]

@[simp] theorem step_wait_req_idle :
    let s : State := { init with state := WAIT_REQ, rdy := true }
    step true s zeroInput = { s with rdy := false } := by
  native_decide

@[simp] theorem step_wait_req_take :
    let s : State := { init with state := WAIT_REQ }
    let i : Input := { din1 := one32, din2 := one32, dval := true }
    step true s i = { s with a := one32, b := one32, rdy := false, state := UNPACK } := by
  native_decide

@[simp] theorem step_unpack_one :
    let s : State := { init with state := UNPACK, a := one32, b := one32 }
    step true s zeroInput =
      { s with
        a_m := bv24 0
        b_m := bv24 0
        a_e := bv10 0
        b_e := bv10 0
        a_s := false
        b_s := false
        state := SPECIAL_CASES } := by
  native_decide

@[simp] theorem step_special_nan :
    let s : State := { init with state := SPECIAL_CASES, a_e := bv10 128, a_m := bv24 1 }
    step true s zeroInput = { s with z := nan32, state := OUT_RDY } := by
  native_decide

@[simp] theorem step_special_inf_times_zero_is_nan :
    let s : State := {
      init with
      state := SPECIAL_CASES
      a_e := bv10 128
      b_e := bv10 897
      b_m := bv24 0
    }
    step true s zeroInput = { s with z := nan32, state := OUT_RDY } := by
  native_decide

@[simp] theorem step_special_normal_path :
    let s : State := {
      init with
      state := SPECIAL_CASES
      a_e := bv10 0
      b_e := bv10 0
      a_m := bv24 0
      b_m := bv24 0
    }
    step true s zeroInput =
      { s with
        a_m := bv24 (2 ^ 23)
        b_m := bv24 (2 ^ 23)
        a_e := bv10 0
        b_e := bv10 0
        state := NORMALISE_A } := by
  native_decide

@[simp] theorem step_normalise_a_done :
    let s : State := { init with state := NORMALISE_A, a_m := bv24 (2 ^ 23) }
    step true s zeroInput = { s with state := NORMALISE_B } := by
  native_decide

@[simp] theorem step_normalise_b_done :
    let s : State := { init with state := NORMALISE_B, b_m := bv24 (2 ^ 23) }
    step true s zeroInput = { s with state := MULTIPLY_0 } := by
  native_decide

@[simp] theorem step_multiply0_one_times_one :
    let s : State := {
      init with
      state := MULTIPLY_0
      a_m := bv24 (2 ^ 23)
      b_m := bv24 (2 ^ 23)
      a_e := bv10 0
      b_e := bv10 0
      a_s := false
      b_s := false
    }
    step true s zeroInput =
      { s with
        z_s := false
        z_e := bv10 1
        product := bv48 (2 ^ 46)
        state := MULTIPLY_1 } := by
  native_decide

@[simp] theorem step_multiply1_one_times_one :
    let s : State := { init with state := MULTIPLY_1, product := bv48 (2 ^ 46) }
    step true s zeroInput =
      { s with
        z_m := bv24 (2 ^ 22)
        guard := false
        round_bit := false
        sticky := false
        state := NORMALISE_1 } := by
  native_decide

@[simp] theorem step_normalise1_shift :
    let s : State := {
      init with
      state := NORMALISE_1
      z_m := bv24 (2 ^ 22)
      z_e := bv10 1
      guard := true
      round_bit := false
    }
    step true s zeroInput =
      { s with
        z_e := bv10 0
        z_m := bv24 ((2 ^ 23) + 1)
        guard := false
        round_bit := false } := by
  native_decide

@[simp] theorem step_normalise2_underflow :
    let s : State := {
      init with
      state := NORMALISE_2
      z_e := bv10 897
      z_m := bv24 (2 ^ 23)
      guard := true
      round_bit := false
      sticky := false
    }
    step true s zeroInput =
      { s with
        z_e := bv10 898
        z_m := bv24 (2 ^ 22)
        guard := false
        round_bit := true
        sticky := false } := by
  native_decide

@[simp] theorem step_round_increment :
    let s : State := {
      init with
      state := ROUND
      z_m := bv24 1
      guard := true
      round_bit := false
      sticky := false
    }
    step true s zeroInput =
      { s with
        z_m := bv24 2
        z_e := bv10 0
        state := PACK } := by
  native_decide

@[simp] theorem step_pack_overflow :
    let s : State := {
      init with
      state := PACK
      z_e := bv10 128
      z_m := bv24 (2 ^ 23)
      z_s := true
    }
    step true s zeroInput =
      { s with z := inf32 true, state := OUT_RDY } := by
  native_decide

@[simp] theorem step_out_rdy :
    let s : State := { init with state := OUT_RDY, z := one32 }
    step true s zeroInput = { s with rdy := true, result := one32, state := WAIT_REQ } := by
  native_decide

end fpu_sp_mul
