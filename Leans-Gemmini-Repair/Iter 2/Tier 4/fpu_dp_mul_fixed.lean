import Std

namespace fpu_dp_mul

inductive FsmState where
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
  state : FsmState
  rdy : Bool
  result : BitVec 64
  a : BitVec 64
  b : BitVec 64
  z : BitVec 64
  a_m : BitVec 53
  b_m : BitVec 53
  z_m : BitVec 53
  a_e : BitVec 13
  b_e : BitVec 13
  z_e : BitVec 13
  a_s : Bool
  b_s : Bool
  z_s : Bool
  guard : Bool
  round_bit : Bool
  sticky : Bool
  product : BitVec 106
deriving Repr, DecidableEq

structure Input where
  rst_n : Bool
  din1 : BitVec 64
  din2 : BitVec 64
  dval : Bool
deriving Repr, DecidableEq

structure Output where
  result : BitVec 64
  rdy : Bool
deriving Repr, DecidableEq

def init : State := {
  state := FsmState.WAIT_REQ
  rdy := false
  result := BitVec.ofNat 64 0
  a := BitVec.ofNat 64 0
  b := BitVec.ofNat 64 0
  z := BitVec.ofNat 64 0
  a_m := BitVec.ofNat 53 0
  b_m := BitVec.ofNat 53 0
  z_m := BitVec.ofNat 53 0
  a_e := BitVec.ofNat 13 0
  b_e := BitVec.ofNat 13 0
  z_e := BitVec.ofNat 13 0
  a_s := false
  b_s := false
  z_s := false
  guard := false
  round_bit := false
  sticky := false
  product := BitVec.ofNat 106 0
}

def step (s : State) (i : Input) : State :=
  if !i.rst_n then
    init
  else
    match s.state with
    | FsmState.WAIT_REQ =>
      if i.dval then
        { s with state := FsmState.UNPACK, rdy := false, a := i.din1, b := i.din2 }
      else
        { s with rdy := false }

    | FsmState.UNPACK =>
      let next_a_m := BitVec.zeroExtend 53 (s.a.extractLsb 51 0)
      let next_b_m := BitVec.zeroExtend 53 (s.b.extractLsb 51 0)
      let next_a_e := BitVec.zeroExtend 13 (s.a.extractLsb 62 52) - BitVec.ofNat 13 1023
      let next_b_e := BitVec.zeroExtend 13 (s.b.extractLsb 62 52) - BitVec.ofNat 13 1023
      let next_a_s := s.a.getLsb 63
      let next_b_s := s.b.getLsb 63
      { s with state := FsmState.SPECIAL_CASES, a_m := next_a_m, b_m := next_b_m, a_e := next_a_e, b_e := next_b_e, a_s := next_a_s, b_s := next_b_s }

    | FsmState.SPECIAL_CASES =>
      let a_e_is_1024 := s.a_e == BitVec.ofNat 13 1024
      let b_e_is_1024 := s.b_e == BitVec.ofNat 13 1024
      let a_e_is_neg1023 := s.a_e.toInt == -1023
      let b_e_is_neg1023 := s.b_e.toInt == -1023
      let a_m_nz := s.a_m != BitVec.ofNat 53 0
      let b_m_nz := s.b_m != BitVec.ofNat 53 0
      let a_m_z := s.a_m == BitVec.ofNat 53 0
      let b_m_z := s.b_m == BitVec.ofNat 53 0

      let nan_z := (BitVec.ofNat 64 1 <<< 63) ||| (BitVec.ofNat 64 2047 <<< 52) ||| (BitVec.ofNat 64 1 <<< 51)
      let sign_diff := if s.a_s != s.b_s then (BitVec.ofNat 64 1 <<< 63) else BitVec.ofNat 64 0
      let z_inf := sign_diff ||| (BitVec.ofNat 64 2047 <<< 52)
      let z_zero := sign_diff

      if (a_e_is_1024 && a_m_nz) || (b_e_is_1024 && b_m_nz) then
        { s with state := FsmState.OUT_RDY, z := nan_z }
      else if a_e_is_1024 then
        let z_final := if b_e_is_neg1023 && b_m_z then nan_z else z_inf
        { s with state := FsmState.OUT_RDY, z := z_final }
      else if b_e_is_1024 then
        let z_final := if a_e_is_neg1023 && a_m_z then nan_z else z_inf
        { s with state := FsmState.OUT_RDY, z := z_final }
      else if a_e_is_neg1023 && a_m_z then
        { s with state := FsmState.OUT_RDY, z := z_zero }
      else if b_e_is_neg1023 && b_m_z then
        { s with state := FsmState.OUT_RDY, z := z_zero }
      else
        let next_a_e := if a_e_is_neg1023 then (BitVec.ofNat 13 0 - BitVec.ofNat 13 1022) else s.a_e
        let next_a_m := if a_e_is_neg1023 then s.a_m else s.a_m ||| (BitVec.ofNat 53 1 <<< 52)
        let next_b_e := if b_e_is_neg1023 then (BitVec.ofNat 13 0 - BitVec.ofNat 13 1022) else s.b_e
        let next_b_m := if b_e_is_neg1023 then s.b_m else s.b_m ||| (BitVec.ofNat 53 1 <<< 52)
        { s with state := FsmState.NORMALISE_A, a_e := next_a_e, a_m := next_a_m, b_e := next_b_e, b_m := next_b_m }

    | FsmState.NORMALISE_A =>
      if s.a_m.getLsb 52 then
        { s with state := FsmState.NORMALISE_B }
      else
        { s with a_m := s.a_m <<< 1, a_e := s.a_e - 1 }

    | FsmState.NORMALISE_B =>
      if s.b_m.getLsb 52 then
        { s with state := FsmState.MULTIPLY_0 }
      else
        { s with b_m := s.b_m <<< 1, b_e := s.b_e - 1 }

    | FsmState.MULTIPLY_0 =>
      let next_z_s := s.a_s != s.b_s
      let next_z_e := s.a_e + s.b_e + 1
      let next_product := BitVec.zeroExtend 106 s.a_m * BitVec.zeroExtend 106 s.b_m
      { s with state := FsmState.MULTIPLY_1, z_s := next_z_s, z_e := next_z_e, product := next_product }

    | FsmState.MULTIPLY_1 =>
      let next_z_m := BitVec.zeroExtend 53 (s.product.extractLsb 105 53)
      let next_guard := s.product.getLsb 52
      let next_round_bit := s.product.getLsb 51
      let next_sticky := BitVec.zeroExtend 51 (s.product.extractLsb 50 0) != BitVec.ofNat 51 0
      { s with state := FsmState.NORMALISE_1, z_m := next_z_m, guard := next_guard, round_bit := next_round_bit, sticky := next_sticky }

    | FsmState.NORMALISE_1 =>
      if !s.z_m.getLsb 52 then
        let next_z_e := s.z_e - 1
        let next_z_m := (s.z_m <<< 1) ||| (if s.guard then BitVec.ofNat 53 1 else BitVec.ofNat 53 0)
        let next_guard := s.round_bit
        { s with z_e := next_z_e, z_m := next_z_m, guard := next_guard, round_bit := false }
      else
        { s with state := FsmState.NORMALISE_2 }

    | FsmState.NORMALISE_2 =>
      if s.z_e.toInt < -1022 then
        let next_z_e := s.z_e + 1
        let next_z_m := s.z_m >>> 1
        let next_guard := s.z_m.getLsb 0
        let next_round_bit := next_guard
        let next_sticky := s.sticky || next_round_bit
        { s with z_e := next_z_e, z_m := next_z_m, guard := next_guard, round_bit := next_round_bit, sticky := next_sticky }
      else
        { s with state := FsmState.ROUND }

    | FsmState.ROUND =>
      if s.guard && (s.round_bit || s.sticky || s.z_m.getLsb 0) then
        let next_z_m := s.z_m + 1
        let next_z_e := if s.z_m == BitVec.ofNat 53 0x1fffffffffffff then s.z_e + 1 else s.z_e
        { s with state := FsmState.PACK, z_m := next_z_m, z_e := next_z_e }
      else
        { s with state := FsmState.PACK }

    | FsmState.PACK =>
      let sign_bit_bv := if s.z_s then BitVec.ofNat 64 1 <<< 63 else BitVec.ofNat 64 0
      let exp_add := BitVec.zeroExtend 12 (s.z_e.extractLsb 11 0) + BitVec.ofNat 12 1023
      let exp_val_bv := (BitVec.zeroExtend 64 (exp_add.extractLsb 10 0)) <<< 52
      let mant_val_bv := BitVec.zeroExtend 64 (s.z_m.extractLsb 51 0)

      let next_z := sign_bit_bv ||| exp_val_bv ||| mant_val_bv

      let next_z2 := if s.z_e.toInt == -1022 && !s.z_m.getLsb 52 then
                       next_z &&& ~~~(BitVec.ofNat 64 2047 <<< 52)
                     else
                       next_z

      let next_z3 := if s.z_e.toInt > 1023 then
                       sign_bit_bv ||| (BitVec.ofNat 64 2047 <<< 52)
                     else
                       next_z2

      { s with state := FsmState.OUT_RDY, z := next_z3 }

    | FsmState.OUT_RDY =>
      { s with rdy := true, result := s.z, state := FsmState.WAIT_REQ }

def out (s : State) : Output :=
  { result := s.result, rdy := s.rdy }

@[simp] theorem step_reset (s : State) (i : Input) :
  i.rst_n = false → step s i = init := by
  intro h; simp [step, h, init]

end fpu_dp_mul
