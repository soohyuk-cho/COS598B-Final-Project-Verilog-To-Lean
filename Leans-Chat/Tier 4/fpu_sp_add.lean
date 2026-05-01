import Std

namespace fpu_sp_add

abbrev Bit := Bool
abbrev Bits3 := BitVec 3
abbrev Bits4 := BitVec 4
abbrev Bits8 := BitVec 8
abbrev Bits10 := BitVec 10
abbrev Bits23 := BitVec 23
abbrev Bits24 := BitVec 24
abbrev Bits27 := BitVec 27
abbrev Bits28 := BitVec 28
abbrev Bits32 := BitVec 32

inductive Phase where
  | WAIT_REQ
  | UNPACK
  | SPECIAL_CASES
  | ALIGN
  | ADD_0
  | ADD_1
  | NORMALISE_1
  | NORMALISE_2
  | ROUND
  | PACK
  | OUT_RDY
  deriving Repr, DecidableEq

structure State where
  phase : Phase
  result : Bits32
  rdy : Bit
  s_output_z : Bits32
  a : Bits32
  b : Bits32
  z : Bits32
  a_m : Bits27
  b_m : Bits27
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
  pre_sum : Bits28
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

def bv3 (n : Nat) : Bits3 := BitVec.ofNat 3 n
def bv8 (n : Nat) : Bits8 := BitVec.ofNat 8 n
def bv10 (n : Nat) : Bits10 := BitVec.ofNat 10 n
def bv10i (n : Int) : Bits10 := BitVec.ofInt 10 n
def bv23 (n : Nat) : Bits23 := BitVec.ofNat 23 n
def bv24 (n : Nat) : Bits24 := BitVec.ofNat 24 n
def bv27 (n : Nat) : Bits27 := BitVec.ofNat 27 n
def bv28 (n : Nat) : Bits28 := BitVec.ofNat 28 n
def bv32 (n : Nat) : Bits32 := BitVec.ofNat 32 n
def bit1 (b : Bit) : BitVec 1 := BitVec.ofNat 1 b.toNat

def frac23 (x : Bits32) : Bits23 := BitVec.extractLsb 22 0 x
def exp8 (x : Bits32) : Bits8 := BitVec.extractLsb 30 23 x
def signBit (x : Bits32) : Bit := x.getLsbD 31
def mant27FromWord (x : Bits32) : Bits27 := BitVec.setWidth 27 (frac23 x ++ bv3 0)
def expUnbias (x : Bits32) : Bits10 := bv10i (Int.ofNat (exp8 x).toNat - 127)
def low8 (x : Bits10) : Bits8 := BitVec.extractLsb 7 0 x
def mantPack23 (x : Bits27) : Bits23 := BitVec.setWidth 23 (BitVec.extractLsb 26 3 x)
def packFloat (sgn : Bit) (exp : Bits8) (frac : Bits23) : Bits32 := bit1 sgn ++ exp ++ frac
def isSignedEq (x : Bits10) (n : Int) : Bool := x.toInt = n
def isSignedLt (x : Bits10) (n : Int) : Bool := x.toInt < n
def isSignedGt (x : Bits10) (n : Int) : Bool := x.toInt > n
def shiftRightSticky27 (x : Bits27) : Bits27 := (x >>> 1) ||| (if x.getLsbD 0 then bv27 1 else bv27 0)
def shiftLeftGuard24 (x : Bits24) (b : Bit) : Bits24 := (x <<< 1) ||| (if b then bv24 1 else bv24 0)
def qNaN : Bits32 := packFloat true (bv8 255) (bv23 (2 ^ 22))
def inf32 (sgn : Bit) : Bits32 := packFloat sgn (bv8 255) (bv23 0)

def init : State :=
  { phase := .WAIT_REQ
    result := bv32 0
    rdy := false
    s_output_z := bv32 0
    a := bv32 0
    b := bv32 0
    z := bv32 0
    a_m := bv27 0
    b_m := bv27 0
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
    pre_sum := bv28 0 }

def step (rst_n : Bit) (s : State) (i : Input) : State :=
  if rst_n = false then
    { s with phase := .WAIT_REQ, rdy := false }
  else
    match s.phase with
    | .WAIT_REQ =>
        let s' := { s with rdy := false }
        if i.dval then
          { s' with a := i.din1, b := i.din2, phase := .UNPACK }
        else
          s'
    | .UNPACK =>
        { s with
            a_m := mant27FromWord s.a
            b_m := mant27FromWord s.b
            a_e := expUnbias s.a
            b_e := expUnbias s.b
            a_s := signBit s.a
            b_s := signBit s.b
            phase := .SPECIAL_CASES }
    | .SPECIAL_CASES =>
        if (s.a_e = bv10i 128 && s.a_m ≠ bv27 0) || (s.b_e = bv10i 128 && s.b_m ≠ bv27 0) then
          { s with z := qNaN, phase := .OUT_RDY }
        else if s.a_e = bv10i 128 then
          let z :=
            if s.b_e = bv10i 128 && s.a_s ≠ s.b_s then qNaN else inf32 s.a_s
          { s with z := z, phase := .OUT_RDY }
        else if s.b_e = bv10i 128 then
          { s with z := inf32 s.b_s, phase := .OUT_RDY }
        else if (isSignedEq s.a_e (-127) && s.a_m = bv27 0) && (isSignedEq s.b_e (-127) && s.b_m = bv27 0) then
          { s with
              z := packFloat (s.a_s && s.b_s) (low8 s.b_e + bv8 127) (mantPack23 s.b_m)
              phase := .OUT_RDY }
        else if isSignedEq s.a_e (-127) && s.a_m = bv27 0 then
          { s with
              z := packFloat s.b_s (low8 s.b_e + bv8 127) (mantPack23 s.b_m)
              phase := .OUT_RDY }
        else if isSignedEq s.b_e (-127) && s.b_m = bv27 0 then
          { s with
              z := packFloat s.a_s (low8 s.a_e + bv8 127) (mantPack23 s.a_m)
              phase := .OUT_RDY }
        else
          let next_ae := if isSignedEq s.a_e (-127) then bv10i (-126) else s.a_e
          let next_be := if isSignedEq s.b_e (-127) then bv10i (-126) else s.b_e
          let next_am := if isSignedEq s.a_e (-127) then s.a_m else s.a_m ||| bv27 (2 ^ 26)
          let next_bm := if isSignedEq s.b_e (-127) then s.b_m else s.b_m ||| bv27 (2 ^ 26)
          { s with a_e := next_ae, b_e := next_be, a_m := next_am, b_m := next_bm, phase := .ALIGN }
    | .ALIGN =>
        if s.a_e.toInt > s.b_e.toInt then
          { s with b_e := s.b_e + bv10 1, b_m := shiftRightSticky27 s.b_m }
        else if s.a_e.toInt < s.b_e.toInt then
          { s with a_e := s.a_e + bv10 1, a_m := shiftRightSticky27 s.a_m }
        else
          { s with phase := .ADD_0 }
    | .ADD_0 =>
        let z_e := s.a_e
        let (pre_sum, z_s) :=
          if s.a_s = s.b_s then
            (BitVec.setWidth 28 s.a_m + BitVec.setWidth 28 s.b_m, s.a_s)
          else if s.a_m.toNat >= s.b_m.toNat then
            (BitVec.setWidth 28 s.a_m - BitVec.setWidth 28 s.b_m, s.a_s)
          else
            (BitVec.setWidth 28 s.b_m - BitVec.setWidth 28 s.a_m, s.b_s)
        { s with z_e := z_e, pre_sum := pre_sum, z_s := z_s, phase := .ADD_1 }
    | .ADD_1 =>
        if s.pre_sum.getLsbD 27 then
          { s with
              z_m := BitVec.extractLsb 27 4 s.pre_sum
              guard := s.pre_sum.getLsbD 3
              round_bit := s.pre_sum.getLsbD 2
              sticky := s.pre_sum.getLsbD 1 || s.pre_sum.getLsbD 0
              z_e := s.z_e + bv10 1
              phase := .NORMALISE_1 }
        else
          { s with
              z_m := BitVec.extractLsb 26 3 s.pre_sum
              guard := s.pre_sum.getLsbD 2
              round_bit := s.pre_sum.getLsbD 1
              sticky := s.pre_sum.getLsbD 0
              phase := .NORMALISE_1 }
    | .NORMALISE_1 =>
        if s.z_m.getLsbD 23 = false && s.z_e.toInt > -126 then
          { s with
              z_e := s.z_e - bv10 1
              z_m := shiftLeftGuard24 s.z_m s.guard
              guard := s.round_bit
              round_bit := false }
        else
          { s with phase := .NORMALISE_2 }
    | .NORMALISE_2 =>
        if s.z_e.toInt < -126 then
          { s with
              z_e := s.z_e + bv10 1
              z_m := s.z_m >>> 1
              guard := s.z_m.getLsbD 0
              round_bit := s.guard
              sticky := s.sticky || s.round_bit }
        else
          { s with phase := .ROUND }
    | .ROUND =>
        if s.guard && (s.round_bit || s.sticky || s.z_m.getLsbD 0) then
          { s with
              z_m := s.z_m + bv24 1
              z_e := if s.z_m = bv24 0xffffff then s.z_e + bv10 1 else s.z_e
              phase := .PACK }
        else
          { s with phase := .PACK }
    | .PACK =>
        let baseFrac : Bits23 := BitVec.extractLsb 22 0 s.z_m
        let baseExp : Bits8 := low8 s.z_e + bv8 127
        let underflowExp : Bits8 := if isSignedEq s.z_e (-126) && s.z_m.getLsbD 23 = false then bv8 0 else baseExp
        let zeroSign : Bit := if isSignedEq s.z_e (-126) && s.z_m = bv24 0 then false else s.z_s
        let frac : Bits23 := if isSignedGt s.z_e 127 then bv23 0 else baseFrac
        let exp : Bits8 := if isSignedGt s.z_e 127 then bv8 255 else underflowExp
        let sgn : Bit := if isSignedGt s.z_e 127 then s.z_s else zeroSign
        { s with z := packFloat sgn exp frac, phase := .OUT_RDY }
    | .OUT_RDY =>
        { s with rdy := true, result := s.z, phase := .WAIT_REQ }

def out (s : State) : Output :=
  { result := s.result, rdy := s.rdy }

@[simp] theorem step_reset (s : State) (i : Input) :
    step false s i = { s with phase := .WAIT_REQ, rdy := false } := by
  simp [step]

theorem step_wait_req_idle :
    step true init { din1 := bv32 7, din2 := bv32 9, dval := false } =
      { init with rdy := false } := by
  native_decide

theorem step_wait_req_accept :
    step true init { din1 := bv32 7, din2 := bv32 9, dval := true } =
      { init with rdy := false, a := bv32 7, b := bv32 9, phase := .UNPACK } := by
  native_decide

theorem step_special_cases_nan :
    step true
      { init with
          phase := .SPECIAL_CASES
          a_e := bv10i 128
          a_m := bv27 1 }
      { din1 := bv32 0, din2 := bv32 0, dval := false } =
      { init with
          phase := .OUT_RDY
          a_e := bv10i 128
          a_m := bv27 1
          z := qNaN } := by
  native_decide

theorem step_out_rdy :
    step true
      { init with
          phase := .OUT_RDY
          z := bv32 123 }
      { din1 := bv32 0, din2 := bv32 0, dval := false } =
      { init with
          phase := .WAIT_REQ
          z := bv32 123
          result := bv32 123
          rdy := true } := by
  native_decide

end fpu_sp_add
