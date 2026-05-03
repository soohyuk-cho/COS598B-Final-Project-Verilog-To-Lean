import Std

namespace fpu_dp_add

inductive FsmState where
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
  state : FsmState
  rdy : Bool
  result : BitVec 64
  a : BitVec 64
  b : BitVec 64
  z : BitVec 64
  a_m : BitVec 56
  b_m : BitVec 56
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
  sum : BitVec 57
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
  a_m := BitVec.ofNat 56 0
  b_m := BitVec.ofNat 56 0
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
  sum := BitVec.ofNat 57 0
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
      let next_a_m := (BitVec.zeroExtend 56 (s.a.extractLsb 51 0)) <<< 3
      let next_b_m := (BitVec.zeroExtend 56 (s.b.extractLsb 51 0)) <<< 3
      let next_a_e := (BitVec.zeroExtend 13 (s.a.extractLsb 62 52)) - BitVec.ofNat 13 1023
      let next_b_e := (BitVec.zeroExtend 13 (s.b.extractLsb 62 52)) - BitVec.ofNat 13 1023
      let next_a_s := s.a.getLsb 63
      let next_b_s := s.b.getLsb 63
      { s with state := FsmState.SPECIAL_CASES, a_m := next_a_m, b_m := next_b_m, a_e := next_a_e, b_e := next_b_e, a_s := next_a_s, b_s := next_b_s }

    | FsmState.SPECIAL_CASES =>
      let a_e_is_1024 := s.a_e == BitVec.ofNat 13 1024
      let b_e_is_1024 := s.b_e == BitVec.ofNat 13 1024
      let a_e_is_neg1023 := s.a_e.toInt == -1023
      let b_e_is_neg1023 := s.b_e.toInt == -1023
      let a_m_neq_0 := s.a_m != BitVec.ofNat 56 0
      let b_m_neq_0 := s.b_m != BitVec.ofNat 56 0
      let a_m_is_0 := s.a_m == BitVec.ofNat 56 0
      let b_m_is_0 := s.b_m == BitVec.ofNat 56 0

      let nan_z := (BitVec.ofNat 64 1 <<< 63) ||| (BitVec.ofNat 64 2047 <<< 52) ||| (BitVec.ofNat 64 1 <<< 51)
      let a_s_bv := if s.a_s then BitVec.ofNat 64 1 <<< 63 else BitVec.ofNat 64 0
      let b_s_bv := if s.b_s then BitVec.ofNat 64 1 <<< 63 else BitVec.ofNat 64 0
      let a_b_s_bv := if s.a_s && s.b_s then BitVec.ofNat 64 1 <<< 63 else BitVec.ofNat 64 0

      let z_a1024_base := a_s_bv ||| (BitVec.ofNat 64 2047 <<< 52)
      let z_a1024 := if b_e_is_1024 && s.a_s != s.b_s then nan_z else z_a1024_base

      let z_b1024 := b_s_bv ||| (BitVec.ofNat 64 2047 <<< 52)

      let z_both_neg1023 := a_b_s_bv ||| (BitVec.zeroExtend 64 (s.b_e + BitVec.ofNat 13 1023).extractLsb 10 0 <<< 52) ||| BitVec.zeroExtend 64 (s.b_m >>> 3).extractLsb 51 0
      let z_a_neg1023 := b_s_bv ||| (BitVec.zeroExtend 64 (s.b_e + BitVec.ofNat 13 1023).extractLsb 10 0 <<< 52) ||| BitVec.zeroExtend 64 (s.b_m >>> 3).extractLsb 51 0
      let z_b_neg1023 := a_s_bv ||| (BitVec.zeroExtend 64 (s.a_e + BitVec.ofNat 13 1023).extractLsb 10 0 <<< 52) ||| BitVec.zeroExtend 64 (s.a_m >>> 3).extractLsb 51 0

      if (a_e_is_1024 && a_m_neq_0) || (b_e_is_1024 && b_m_neq_0) then
        { s with state := FsmState.OUT_RDY, z := nan_z }
      else if a_e_is_1024 then
        { s with state := FsmState.OUT_RDY, z := z_a1024 }
      else if b_e_is_1024 then
        { s with state := FsmState.OUT_RDY, z := z_b1024 }
      else if a_e_is_neg1023 && a_m_is_0 && b_e_is_neg1023 && b_m_is_0 then
        { s with state := FsmState.OUT_RDY, z := z_both_neg1023 }
      else if a_e_is_neg1023 && a_m_is_0 then
        { s with state := FsmState.OUT_RDY, z := z_a_neg1023 }
      else if b_e_is_neg1023 && b_m_is_0 then
        { s with state := FsmState.OUT_RDY, z := z_b_neg1023 }
      else
        let next_a_e := if a_e_is_neg1023 then (BitVec.ofNat 13 0 - BitVec.ofNat 13 1022) else s.a_e
        let next_a_m := if a_e_is_neg1023 then s.a_m else s.a_m ||| (BitVec.ofNat 56 1 <<< 55)
        let next_b_e := if b_e_is_neg1023 then (BitVec.ofNat 13 0 - BitVec.ofNat 13 1022) else s.b_e
        let next_b_m := if b_e_is_neg1023 then s.b_m else s.b_m ||| (BitVec.ofNat 56 1 <<< 55)
        { s with state := FsmState.ALIGN, a_e := next_a_e, a_m := next_a_m, b_e := next_b_e, b_m := next_b_m }

    | FsmState.ALIGN =>
      if s.a_e.toInt > s.b_e.toInt then
        let next_b_e := s.b_e + 1
        let b_m_shifted := s.b_m >>> 1
        let bit0 := s.b_m.getLsb 0 || s.b_m.getLsb 1
        let next_b_m := if bit0 then b_m_shifted ||| BitVec.ofNat 56 1 else b_m_shifted &&& ~~~(BitVec.ofNat 56 1)
        { s with b_e := next_b_e, b_m := next_b_m }
      else if s.a_e.toInt < s.b_e.toInt then
        let next_a_e := s.a_e + 1
        let a_m_shifted := s.a_m >>> 1
        let bit0 := s.a_m.getLsb 0 || s.a_m.getLsb 1
        let next_a_m := if bit0 then a_m_shifted ||| BitVec.ofNat 56 1 else a_m_shifted &&& ~~~(BitVec.ofNat 56 1)
        { s with a_e := next_a_e, a_m := next_a_m }
      else
        { s with state := FsmState.ADD_0 }

    | FsmState.ADD_0 =>
      let next_z_e := s.a_e
      if s.a_s == s.b_s then
        let next_sum := (BitVec.zeroExtend 57 s.a_m) + (BitVec.zeroExtend 57 s.b_m)
        { s with state := FsmState.ADD_1, z_e := next_z_e, sum := next_sum, z_s := s.a_s }
      else
        if s.a_m >= s.b_m then
          let next_sum := (BitVec.zeroExtend 57 s.a_m) - (BitVec.zeroExtend 57 s.b_m)
          { s with state := FsmState.ADD_1, z_e := next_z_e, sum := next_sum, z_s := s.a_s }
        else
          let next_sum := (BitVec.zeroExtend 57 s.b_m) - (BitVec.zeroExtend 57 s.a_m)
          { s with state := FsmState.ADD_1, z_e := next_z_e, sum := next_sum, z_s := s.b_s }

    | FsmState.ADD_1 =>
      if s.sum.getLsb 56 then
        let next_z_m := BitVec.zeroExtend 53 (s.sum.extractLsb 56 4)
        let next_guard := s.sum.getLsb 3
        let next_round_bit := s.sum.getLsb 2
        let next_sticky := s.sum.getLsb 1 || s.sum.getLsb 0
        let next_z_e := s.z_e + 1
        { s with state := FsmState.NORMALISE_1, z_m := next_z_m, guard := next_guard, round_bit := next_round_bit, sticky := next_sticky, z_e := next_z_e }
      else
        let next_z_m := BitVec.zeroExtend 53 (s.sum.extractLsb 55 3)
        let next_guard := s.sum.getLsb 2
        let next_round_bit := s.sum.getLsb 1
        let next_sticky := s.sum.getLsb 0
        { s with state := FsmState.NORMALISE_1, z_m := next_z_m, guard := next_guard, round_bit := next_round_bit, sticky := next_sticky }

    | FsmState.NORMALISE_1 =>
      if !s.z_m.getLsb 52 && s.z_e.toInt > -1022 then
        let next_z_e := s.z_e - 1
        let next_z_m := (s.z_m <<< 1) ||| (if s.guard then BitVec.ofNat 53 1 else BitVec.ofNat 53 0)
        let next_guard := s.round_bit
        let next_round_bit := false
        { s with z_e := next_z_e, z_m := next_z_m, guard := next_guard, round_bit := next_round_bit }
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
      let exp_add := BitVec.zeroExtend 13 (s.z_e + BitVec.ofNat 13 1023)
      let exp_val_bv := (BitVec.zeroExtend 64 (exp_add.extractLsb 10 0)) <<< 52
      let mant_val_bv := BitVec.zeroExtend 64 (s.z_m.extractLsb 51 0)

      let z_base := sign_bit_bv ||| exp_val_bv ||| mant_val_bv

      let z1 := if s.z_e.toInt == -1022 && !s.z_m.getLsb 52 then
                  z_base &&& ~~~(BitVec.ofNat 64 2047 <<< 52)
                else
                  z_base
      let z2 := if s.z_e.toInt == -1022 && s.z_m == BitVec.ofNat 53 0 then
                  z1 &&& ~~~(BitVec.ofNat 64 1 <<< 63)
                else
                  z1
      let z3 := if s.z_e.toInt > 1023 then
                  sign_bit_bv ||| (BitVec.ofNat 64 2047 <<< 52)
                else
                  z2

      { s with state := FsmState.OUT_RDY, z := z3 }

    | FsmState.OUT_RDY =>
      { s with rdy := true, result := s.z, state := FsmState.WAIT_REQ }

def out (s : State) : Output :=
  { result := s.result, rdy := s.rdy }

@[simp] theorem step_reset (s : State) (d1 d2 : BitVec 64) (dv : Bool) :
  step s { rst_n := false, din1 := d1, din2 := d2, dval := dv } = init := by
  rfl

end fpu_dp_add
