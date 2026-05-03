import Std

namespace fpu_dp_div

inductive FsmState where
  | WAIT_REQ
  | UNPACK
  | SPECIAL_CASES
  | NORMALISE_A
  | NORMALISE_B
  | DIVIDE_0
  | DIVIDE_1
  | DIVIDE_2
  | DIVIDE_3
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
  quotient : BitVec 109
  divisor : BitVec 109
  dividend : BitVec 109
  remainder : BitVec 109
  count : BitVec 7
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
  result := 0
  a := 0
  b := 0
  z := 0
  a_m := 0
  b_m := 0
  z_m := 0
  a_e := 0
  b_e := 0
  z_e := 0
  a_s := false
  b_s := false
  z_s := false
  guard := false
  round_bit := false
  sticky := false
  quotient := 0
  divisor := 0
  dividend := 0
  remainder := 0
  count := 0
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
      let next_a_e := (BitVec.zeroExtend 13 (s.a.extractLsb 62 52)) - 1023
      let next_b_e := (BitVec.zeroExtend 13 (s.b.extractLsb 62 52)) - 1023
      let next_a_s := s.a.getLsb 63
      let next_b_s := s.b.getLsb 63
      { s with state := FsmState.SPECIAL_CASES, a_m := next_a_m, b_m := next_b_m, a_e := next_a_e, b_e := next_b_e, a_s := next_a_s, b_s := next_b_s }

    | FsmState.SPECIAL_CASES =>
      let a_e_1024 := s.a_e.toInt == 1024
      let b_e_1024 := s.b_e.toInt == 1024
      let a_e_n1023 := s.a_e.toInt == -1023
      let b_e_n1023 := s.b_e.toInt == -1023
      let a_m_nz := s.a_m != 0
      let b_m_nz := s.b_m != 0
      let a_m_z := s.a_m == 0
      let b_m_z := s.b_m == 0

      let nan_z := BitVec.ofNat 64 0 |>.setBit 63 |>.setLsb 62 52 2047 |>.setBit 51

      if (a_e_1024 && a_m_nz) || (b_e_1024 && b_m_nz) then
        { s with state := FsmState.OUT_RDY, z := nan_z }
      else if a_e_1024 && b_e_1024 then
        { s with state := FsmState.OUT_RDY, z := nan_z }
      else if a_e_1024 then
        let z_base := BitVec.ofNat 64 0 |>.setLsb 63 (s.a_s ^ s.b_s) |>.setLsb 62 52 2047
        let z_final := if b_e_n1023 && b_m_z then nan_z else z_base
        { s with state := FsmState.OUT_RDY, z := z_final }
      else if b_e_1024 then
        let z_final := BitVec.ofNat 64 0 |>.setLsb 63 (s.a_s ^ s.b_s) |>.setLsb 62 52 0
        { s with state := FsmState.OUT_RDY, z := z_final }
      else if a_e_n1023 && a_m_z then
        let z_base := BitVec.ofNat 64 0 |>.setLsb 63 (s.a_s ^ s.b_s) |>.setLsb 62 52 0
        let z_final := if b_e_n1023 && b_m_z then nan_z else z_base
        { s with state := FsmState.OUT_RDY, z := z_final }
      else if b_e_n1023 && b_m_z then
        let z_final := BitVec.ofNat 64 0 |>.setLsb 63 (s.a_s ^ s.b_s) |>.setLsb 62 52 2047
        { s with state := FsmState.OUT_RDY, z := z_final }
      else
        let next_a_e := if a_e_n1023 then (BitVec.ofNat 13 0 - 1022) else s.a_e
        let next_a_m := if a_e_n1023 then s.a_m else s.a_m.setBit 52
        let next_b_e := if b_e_n1023 then (BitVec.ofNat 13 0 - 1022) else s.b_e
        let next_b_m := if b_e_n1023 then s.b_m else s.b_m.setBit 52
        { s with state := FsmState.NORMALISE_A, a_e := next_a_e, a_m := next_a_m, b_e := next_b_e, b_m := next_b_m }

    | FsmState.NORMALISE_A =>
      if s.a_m.getLsb 52 then
        { s with state := FsmState.NORMALISE_B }
      else
        { s with a_m := s.a_m <<< 1, a_e := s.a_e - 1 }

    | FsmState.NORMALISE_B =>
      if s.b_m.getLsb 52 then
        { s with state := FsmState.DIVIDE_0 }
      else
        { s with b_m := s.b_m <<< 1, b_e := s.b_e - 1 }

    | FsmState.DIVIDE_0 =>
      { s with
        state := FsmState.DIVIDE_1,
        z_s := s.a_s ^ s.b_s,
        z_e := s.a_e - s.b_e,
        quotient := 0,
        remainder := 0,
        count := 0,
        dividend := BitVec.zeroExtend 109 s.a_m <<< 56,
        divisor := BitVec.zeroExtend 109 s.b_m }

    | FsmState.DIVIDE_1 =>
      let next_quotient := s.quotient <<< 1
      let next_remainder := (s.remainder <<< 1) | (if s.dividend.getLsb 108 then 1 else 0)
      let next_dividend := s.dividend <<< 1
      { s with state := FsmState.DIVIDE_2, quotient := next_quotient, remainder := next_remainder, dividend := next_dividend }

    | FsmState.DIVIDE_2 =>
      let cond := s.remainder >= s.divisor
      let next_quotient := if cond then s.quotient.setBit 0 else s.quotient
      let next_remainder := if cond then s.remainder - s.divisor else s.remainder
      if s.count == 107 then
        { s with state := FsmState.DIVIDE_3, quotient := next_quotient, remainder := next_remainder }
      else
        { s with state := FsmState.DIVIDE_1, count := s.count + 1, quotient := next_quotient, remainder := next_remainder }

    | FsmState.DIVIDE_3 =>
      { s with
        state := FsmState.NORMALISE_1,
        z_m := s.quotient.extractLsb 55 3 |>.zeroExtend 53,
        guard := s.quotient.getLsb 2,
        round_bit := s.quotient.getLsb 1,
        sticky := s.quotient.getLsb 0 || (s.remainder != 0) }

    | FsmState.NORMALISE_1 =>
      if !s.z_m.getLsb 52 && s.z_e.toInt > -1022 then
        { s with
          z_e := s.z_e - 1,
          z_m := (s.z_m <<< 1) | (if s.guard then 1 else 0),
          guard := s.round_bit,
          round_bit := false }
      else
        { s with state := FsmState.NORMALISE_2 }

    | FsmState.NORMALISE_2 =>
      if s.z_e.toInt < -1022 then
        { s with
          z_e := s.z_e + 1,
          z_m := s.z_m >>> 1,
          guard := s.z_m.getLsb 0,
          round_bit := s.z_m.getLsb 0, -- Actually guard is z_m[0] before shift
          sticky := s.sticky || s.z_m.getLsb 0 }
      else
        { s with state := FsmState.ROUND }

    | FsmState.ROUND =>
      if s.guard && (s.round_bit || s.sticky || s.z_m.getLsb 0) then
        let next_z_m := s.z_m + 1
        let next_z_e := if s.z_m == 0x1fffffffffffff then s.z_e + 1 else s.z_e
        { s with state := FsmState.PACK, z_m := next_z_m, z_e := next_z_e }
      else
        { s with state := FsmState.PACK }

    | FsmState.PACK =>
      let mut next_z := BitVec.ofNat 64 0
      next_z := next_z.setBit 63 s.z_s
      next_z := next_z.setLsb 62 52 (BitVec.zeroExtend 11 (s.z_e + 1023))
      next_z := next_z.setLsb 51 0 (BitVec.zeroExtend 52 s.z_m)

      if s.z_e.toInt == -1022 && !s.z_m.getLsb 52 then
        next_z := next_z.setLsb 62 52 0

      if s.z_e.toInt > 1023 then
        next_z := BitVec.ofNat 64 0 |>.setLsb 63 s.z_s |>.setLsb 62 52 2047

      { s with state := FsmState.OUT_RDY, z := next_z }

    | FsmState.OUT_RDY =>
      { s with rdy := true, result := s.z, state := FsmState.WAIT_REQ }

def out (s : State) : Output :=
  { result := s.result, rdy := s.rdy }

end fpu_dp_div
