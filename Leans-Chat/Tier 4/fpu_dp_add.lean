import Std

namespace fpu_dp_add

abbrev Bit := Bool
abbrev Bits4 := BitVec 4
abbrev Bits11 := BitVec 11
abbrev Bits13 := BitVec 13
abbrev Bits52 := BitVec 52
abbrev Bits53 := BitVec 53
abbrev Bits56 := BitVec 56
abbrev Bits57 := BitVec 57
abbrev Bits64 := BitVec 64

def bv4 (n : Nat) : Bits4 := BitVec.ofNat 4 n
def bv11 (n : Nat) : Bits11 := BitVec.ofNat 11 n
def bv13 (n : Nat) : Bits13 := BitVec.ofNat 13 n
def bv52 (n : Nat) : Bits52 := BitVec.ofNat 52 n
def bv53 (n : Nat) : Bits53 := BitVec.ofNat 53 n
def bv56 (n : Nat) : Bits56 := BitVec.ofNat 56 n
def bv57 (n : Nat) : Bits57 := BitVec.ofNat 57 n
def bv64 (n : Nat) : Bits64 := BitVec.ofNat 64 n

def WAIT_REQ : Bits4 := bv4 0
def UNPACK : Bits4 := bv4 1
def SPECIAL_CASES : Bits4 := bv4 2
def ALIGN : Bits4 := bv4 3
def ADD_0 : Bits4 := bv4 4
def ADD_1 : Bits4 := bv4 5
def NORMALISE_1 : Bits4 := bv4 6
def NORMALISE_2 : Bits4 := bv4 7
def ROUND : Bits4 := bv4 8
def PACK : Bits4 := bv4 9
def OUT_RDY : Bits4 := bv4 10

def twoPow (n : Nat) : Nat := 2 ^ n

def boolToNat (b : Bit) : Nat := if b then 1 else 0

def eqb {α : Type} [DecidableEq α] (a b : α) : Bit := decide (a = b)
def neqb {α : Type} [DecidableEq α] (a b : α) : Bit := decide (a ≠ b)

def bvToInt {w : Nat} (x : BitVec w) : Int :=
  let n := x.toNat
  if n < twoPow (w - 1) then
    Int.ofNat n
  else
    Int.ofNat n - Int.ofNat (twoPow w)

def sgt13 (x y : Bits13) : Bit := decide (bvToInt x > bvToInt y)
def slt13 (x y : Bits13) : Bit := decide (bvToInt x < bvToInt y)
def seq13 (x : Bits13) (n : Int) : Bit := decide (bvToInt x = n)
def sgtConst13 (x : Bits13) (n : Int) : Bit := decide (bvToInt x > n)
def sltConst13 (x : Bits13) (n : Int) : Bit := decide (bvToInt x < n)
def gtu {w : Nat} (x y : BitVec w) : Bit := decide (x.toNat > y.toNat)

def getBit {w : Nat} (x : BitVec w) (i : Nat) : Bit :=
  decide (((x.toNat / twoPow i) % 2) = 1)

def slice {w : Nat} (x : BitVec w) (lo len : Nat) : BitVec len :=
  BitVec.ofNat len ((x.toNat / twoPow lo) % twoPow len)

def lsr {w : Nat} (x : BitVec w) (n : Nat) : BitVec w :=
  BitVec.ofNat w (x.toNat / twoPow n)

def lsl {w : Nat} (x : BitVec w) (n : Nat) : BitVec w :=
  BitVec.ofNat w (x.toNat * twoPow n)

def setBit {w : Nat} (x : BitVec w) (i : Nat) (b : Bit) : BitVec w :=
  let cur := boolToNat (getBit x i)
  let base := x.toNat - cur * twoPow i
  BitVec.ofNat w (base + boolToNat b * twoPow i)

def setSlice {w n : Nat} (x : BitVec w) (lo len : Nat) (v : BitVec n) : BitVec w :=
  let lower := x.toNat % twoPow lo
  let upper := x.toNat / twoPow (lo + len)
  BitVec.ofNat w (lower + v.toNat * twoPow lo + upper * twoPow (lo + len))

def mkFloat (sgn : Bit) (exp : Bits11) (frac : Bits52) : Bits64 :=
  let x0 : Bits64 := bv64 0
  let x1 := setSlice x0 0 52 frac
  let x2 := setSlice x1 52 11 exp
  setBit x2 63 sgn

def qnan : Bits64 := mkFloat true (bv11 2047) (bv52 (twoPow 51))
def inf64 (sgn : Bit) : Bits64 := mkFloat sgn (bv11 2047) (bv52 0)

structure State where
  state : Bits4
  a : Bits64
  b : Bits64
  z : Bits64
  a_m : Bits56
  b_m : Bits56
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
  sum : Bits57
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
    a := bv64 0
    b := bv64 0
    z := bv64 0
    a_m := bv56 0
    b_m := bv56 0
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
    sum := bv57 0
    result := bv64 0
    rdy := false }

def step (s : State) (rst_n : Bit) (i : Input) : State :=
  if !rst_n then
    { s with state := WAIT_REQ, rdy := false }
  else if s.state = WAIT_REQ then
    if i.dval then
      { s with rdy := false, a := i.din1, b := i.din2, state := UNPACK }
    else
      { s with rdy := false }
  else if s.state = UNPACK then
    { s with
        a_m := bv56 ((slice s.a 0 52).toNat * twoPow 3)
        b_m := bv56 ((slice s.b 0 52).toNat * twoPow 3)
        a_e := bv13 ((slice s.a 52 11).toNat + twoPow 13 - 1023)
        b_e := bv13 ((slice s.b 52 11).toNat + twoPow 13 - 1023)
        a_s := getBit s.a 63
        b_s := getBit s.b 63
        state := SPECIAL_CASES }
  else if s.state = SPECIAL_CASES then
    let aNaN := eqb s.a_e (bv13 1024) && neqb s.a_m (bv56 0)
    let bNaN := eqb s.b_e (bv13 1024) && neqb s.b_m (bv56 0)
    let bothZero := seq13 s.a_e (-1023) && eqb s.a_m (bv56 0) &&
      seq13 s.b_e (-1023) && eqb s.b_m (bv56 0)
    let aZero := seq13 s.a_e (-1023) && eqb s.a_m (bv56 0)
    let bZero := seq13 s.b_e (-1023) && eqb s.b_m (bv56 0)
    if aNaN || bNaN then
      { s with z := qnan, state := OUT_RDY }
    else if eqb s.a_e (bv13 1024) then
      let z0 := inf64 s.a_s
      let z1 := if eqb s.b_e (bv13 1024) && (s.a_s != s.b_s) then qnan else z0
      { s with z := z1, state := OUT_RDY }
    else if eqb s.b_e (bv13 1024) then
      { s with z := inf64 s.b_s, state := OUT_RDY }
    else if bothZero then
      { s with
          z := mkFloat (s.a_s && s.b_s) (bv11 ((slice s.b_e 0 11).toNat + 1023)) (bv52 (s.b_m.toNat / twoPow 3))
          state := OUT_RDY }
    else if aZero then
      { s with
          z := mkFloat s.b_s (bv11 ((slice s.b_e 0 11).toNat + 1023)) (bv52 (s.b_m.toNat / twoPow 3))
          state := OUT_RDY }
    else if bZero then
      { s with
          z := mkFloat s.a_s (bv11 ((slice s.a_e 0 11).toNat + 1023)) (bv52 (s.a_m.toNat / twoPow 3))
          state := OUT_RDY }
    else
      let a_e' := if seq13 s.a_e (-1023) then bv13 7170 else s.a_e
      let a_m' := if seq13 s.a_e (-1023) then s.a_m else setBit s.a_m 55 true
      let b_e' := if seq13 s.b_e (-1023) then bv13 7170 else s.b_e
      let b_m' := if seq13 s.b_e (-1023) then s.b_m else setBit s.b_m 55 true
      { s with a_e := a_e', a_m := a_m', b_e := b_e', b_m := b_m', state := ALIGN }
  else if s.state = ALIGN then
    if sgt13 s.a_e s.b_e then
      { s with
          b_e := bv13 (s.b_e.toNat + 1)
          b_m := setBit (lsr s.b_m 1) 0 (getBit s.b_m 0 || getBit s.b_m 1) }
    else if slt13 s.a_e s.b_e then
      { s with
          a_e := bv13 (s.a_e.toNat + 1)
          a_m := setBit (lsr s.a_m 1) 0 (getBit s.a_m 0 || getBit s.a_m 1) }
    else
      { s with state := ADD_0 }
  else if s.state = ADD_0 then
    let sameSign := s.a_s == s.b_s
    let sum' :=
      if sameSign then
        bv57 (s.a_m.toNat + s.b_m.toNat)
      else if gtu s.a_m s.b_m then
        bv57 (s.a_m.toNat - s.b_m.toNat)
      else
        bv57 (s.b_m.toNat - s.a_m.toNat)
    let z_s' :=
      if sameSign then s.a_s else if gtu s.a_m s.b_m then s.a_s else s.b_s
    { s with z_e := s.a_e, sum := sum', z_s := z_s', state := ADD_1 }
  else if s.state = ADD_1 then
    if getBit s.sum 56 then
      { s with
          z_m := slice s.sum 4 53
          guard := getBit s.sum 3
          round_bit := getBit s.sum 2
          sticky := getBit s.sum 1 || getBit s.sum 0
          z_e := bv13 (s.z_e.toNat + 1)
          state := NORMALISE_1 }
    else
      { s with
          z_m := slice s.sum 3 53
          guard := getBit s.sum 2
          round_bit := getBit s.sum 1
          sticky := getBit s.sum 0
          state := NORMALISE_1 }
  else if s.state = NORMALISE_1 then
    if (!getBit s.z_m 52) && sgtConst13 s.z_e (-1022) then
      { s with
          z_e := bv13 (s.z_e.toNat + twoPow 13 - 1)
          z_m := setBit (lsl s.z_m 1) 0 s.guard
          guard := s.round_bit
          round_bit := false }
    else
      { s with state := NORMALISE_2 }
  else if s.state = NORMALISE_2 then
    if sltConst13 s.z_e (-1022) then
      { s with
          z_e := bv13 (s.z_e.toNat + 1)
          z_m := lsr s.z_m 1
          guard := getBit s.z_m 0
          round_bit := s.guard
          sticky := s.sticky || s.round_bit }
    else
      { s with state := ROUND }
  else if s.state = ROUND then
    let roundUp := s.guard && (s.round_bit || s.sticky || getBit s.z_m 0)
    let z_m' := if roundUp then bv53 (s.z_m.toNat + 1) else s.z_m
    let z_e' := if roundUp && s.z_m = bv53 ((twoPow 53) - 1) then bv13 (s.z_e.toNat + 1) else s.z_e
    { s with z_m := z_m', z_e := z_e', state := PACK }
  else if s.state = PACK then
    let z0 := mkFloat s.z_s (bv11 ((slice s.z_e 0 11).toNat + 1023)) (slice s.z_m 0 52)
    let z1 := if seq13 s.z_e (-1022) && !getBit s.z_m 52 then
      setSlice z0 52 11 (bv11 0)
    else
      z0
    let z2 := if seq13 s.z_e (-1022) && eqb s.z_m (bv53 0) then
      setBit z1 63 false
    else
      z1
    let z3 := if sgtConst13 s.z_e 1023 then
      mkFloat s.z_s (bv11 2047) (bv52 0)
    else
      z2
    { s with z := z3, state := OUT_RDY }
  else if s.state = OUT_RDY then
    { s with rdy := true, result := s.z, state := WAIT_REQ }
  else
    s

def out (s : State) : Output :=
  { result := s.result, rdy := s.rdy }

@[simp] theorem step_reset (s : State) (i : Input) :
    step s false i = { s with state := WAIT_REQ, rdy := false } := by
  simp [step]

@[simp] theorem step_wait_req_idle :
    step init true { din1 := bv64 1, din2 := bv64 2, dval := false } =
      { init with rdy := false } := by
  native_decide

@[simp] theorem step_wait_req_latch :
    step init true { din1 := bv64 1, din2 := bv64 2, dval := true } =
      { init with rdy := false, a := bv64 1, b := bv64 2, state := UNPACK } := by
  native_decide

@[simp] theorem step_unpack_basic :
    step
      { init with state := UNPACK, a := bv64 4607182418800017408, b := bv64 4611686018427387904 }
      true
      { din1 := bv64 0, din2 := bv64 0, dval := false } =
      { init with
          state := SPECIAL_CASES
          a := bv64 4607182418800017408
          b := bv64 4611686018427387904
          a_m := bv56 0
          b_m := bv56 0
          a_e := bv13 0
          b_e := bv13 1
          a_s := false
          b_s := false } := by
  native_decide

@[simp] theorem step_special_cases_nan :
    step
      { init with state := SPECIAL_CASES, a_e := bv13 1024, a_m := bv56 1 }
      true
      { din1 := bv64 0, din2 := bv64 0, dval := false } =
      { init with state := OUT_RDY, a_e := bv13 1024, a_m := bv56 1, z := qnan } := by
  native_decide

@[simp] theorem step_align_equal :
    step
      { init with state := ALIGN, a_e := bv13 5, b_e := bv13 5 }
      true
      { din1 := bv64 0, din2 := bv64 0, dval := false } =
      { init with state := ADD_0, a_e := bv13 5, b_e := bv13 5 } := by
  native_decide

@[simp] theorem step_add0_same_sign :
    step
      { init with state := ADD_0, a_e := bv13 7, a_m := bv56 3, b_m := bv56 4, a_s := false, b_s := false }
      true
      { din1 := bv64 0, din2 := bv64 0, dval := false } =
      { init with
          state := ADD_1
          a_e := bv13 7
          a_m := bv56 3
          b_m := bv56 4
          z_e := bv13 7
          a_s := false
          b_s := false
          z_s := false
          sum := bv57 7 } := by
  native_decide

@[simp] theorem step_add1_carry :
    step
      { init with state := ADD_1, z_e := bv13 9, sum := bv57 (twoPow 56) }
      true
      { din1 := bv64 0, din2 := bv64 0, dval := false } =
      { init with
          state := NORMALISE_1
          z_m := bv53 (twoPow 52)
          z_e := bv13 10
          guard := false
          round_bit := false
          sticky := false
          sum := bv57 (twoPow 56) } := by
  native_decide

@[simp] theorem step_normalise1_shift :
    step
      { init with state := NORMALISE_1, z_e := bv13 0, z_m := bv53 1, guard := true }
      true
      { din1 := bv64 0, din2 := bv64 0, dval := false } =
      { init with
          state := NORMALISE_1
          z_e := bv13 (twoPow 13 - 1)
          z_m := bv53 3
          guard := false
          round_bit := false } := by
  native_decide

@[simp] theorem step_normalise2_shift :
    step
      { init with state := NORMALISE_2, z_e := bv13 7169, z_m := bv53 4, guard := true, round_bit := false }
      true
      { din1 := bv64 0, din2 := bv64 0, dval := false } =
      { init with
          state := NORMALISE_2
          z_e := bv13 7170
          z_m := bv53 2
          guard := false
          round_bit := true
          sticky := false } := by
  native_decide

@[simp] theorem step_round_increment :
    step
      { init with state := ROUND, z_m := bv53 3, guard := true }
      true
      { din1 := bv64 0, din2 := bv64 0, dval := false } =
      { init with state := PACK, z_m := bv53 4, guard := true } := by
  native_decide

@[simp] theorem step_pack_overflow :
    step
      { init with state := PACK, z_e := bv13 1024, z_s := true, z_m := bv53 0 }
      true
      { din1 := bv64 0, din2 := bv64 0, dval := false } =
      { init with state := OUT_RDY, z_e := bv13 1024, z_s := true, z_m := bv53 0, z := inf64 true } := by
  native_decide

@[simp] theorem step_out_rdy :
    step { init with state := OUT_RDY, z := bv64 7 } true { din1 := bv64 0, din2 := bv64 0, dval := false } =
      { init with state := WAIT_REQ, z := bv64 7, result := bv64 7, rdy := true } := by
  native_decide

end fpu_dp_add
