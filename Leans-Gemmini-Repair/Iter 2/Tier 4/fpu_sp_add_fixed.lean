import Std

namespace fpu_sp_add

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
  result : BitVec 32
  a : BitVec 32
  b : BitVec 32
  z : BitVec 32
  a_m : BitVec 27
  b_m : BitVec 27
  z_m : BitVec 24
  a_e : BitVec 10
  b_e : BitVec 10
  z_e : BitVec 10
  a_s : Bool
  b_s : Bool
  z_s : Bool
  guard : Bool
  round_bit : Bool
  sticky : Bool
  pre_sum : BitVec 28
deriving Repr, DecidableEq

structure Input where
  rst_n : Bool
  din1 : BitVec 32
  din2 : BitVec 32
  dval : Bool
deriving Repr, DecidableEq

structure Output where
  result : BitVec 32
  rdy : Bool
deriving Repr, DecidableEq

def init : State := {
  state := FsmState.WAIT_REQ
  rdy := false
  result := BitVec.ofNat 32 0
  a := BitVec.ofNat 32 0
  b := BitVec.ofNat 32 0
  z := BitVec.ofNat 32 0
  a_m := BitVec.ofNat 27 0
  b_m := BitVec.ofNat 27 0
  z_m := BitVec.ofNat 24 0
  a_e := BitVec.ofNat 10 0
  b_e := BitVec.ofNat 10 0
  z_e := BitVec.ofNat 10 0
  a_s := false
  b_s := false
  z_s := false
  guard := false
  round_bit := false
  sticky := false
  pre_sum := BitVec.ofNat 28 0
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
      let next_a_m := (BitVec.zeroExtend 27 (s.a.extractLsb 22 0)) <<< 3
      let next_b_m := (BitVec.zeroExtend 27 (s.b.extractLsb 22 0)) <<< 3
      let next_a_e := (BitVec.zeroExtend 10 (s.a.extractLsb 30 23)) - BitVec.ofNat 10 127
      let next_b_e := (BitVec.zeroExtend 10 (s.b.extractLsb 30 23)) - BitVec.ofNat 10 127
      let next_a_s := s.a.getLsb 31
      let next_b_s := s.b.getLsb 31
      { s with state := FsmState.SPECIAL_CASES, a_m := next_a_m, b_m := next_b_m, a_e := next_a_e, b_e := next_b_e, a_s := next_a_s, b_s := next_b_s }

    | FsmState.SPECIAL_CASES =>
      let a_e_is_128 := s.a_e == BitVec.ofNat 10 128
      let b_e_is_128 := s.b_e == BitVec.ofNat 10 128
      let a_e_is_neg127 := s.a_e.toInt == -127
      let b_e_is_neg127 := s.b_e.toInt == -127
      let a_m_neq_0 := s.a_m != BitVec.ofNat 27 0
      let b_m_neq_0 := s.b_m != BitVec.ofNat 27 0
      let a_m_is_0 := s.a_m == BitVec.ofNat 27 0
      let b_m_is_0 := s.b_m == BitVec.ofNat 27 0

      let nan_z := (BitVec.ofNat 32 1 <<< 31) ||| (BitVec.ofNat 32 255 <<< 23) ||| (BitVec.ofNat 32 1 <<< 22)

      let next_z_a128_base := (if s.a_s then BitVec.ofNat 32 1 <<< 31 else BitVec.ofNat 32 0) ||| (BitVec.ofNat 32 255 <<< 23)
      let next_z_a128 := if b_e_is_128 && s.a_s != s.b_s then nan_z else next_z_a128_base

      let next_z_b128 := (if s.b_s then BitVec.ofNat 32 1 <<< 31 else BitVec.ofNat 32 0) ||| (BitVec.ofNat 32 255 <<< 23)

      let next_z_both_zero := (if s.a_s && s.b_s then BitVec.ofNat 32 1 <<< 31 else BitVec.ofNat 32 0) ||| (BitVec.zeroExtend 32 (BitVec.zeroExtend 8 (s.b_e + BitVec.ofNat 10 127)) <<< 23) ||| BitVec.zeroExtend 32 (s.b_m >>> 3)
      let next_z_a_zero := (if s.b_s then BitVec.ofNat 32 1 <<< 31 else BitVec.ofNat 32 0) ||| (BitVec.zeroExtend 32 (BitVec.zeroExtend 8 (s.b_e + BitVec.ofNat 10 127)) <<< 23) ||| BitVec.zeroExtend 32 (s.b_m >>> 3)
      let next_z_b_zero := (if s.a_s then BitVec.ofNat 32 1 <<< 31 else BitVec.ofNat 32 0) ||| (BitVec.zeroExtend 32 (BitVec.zeroExtend 8 (s.a_e + BitVec.ofNat 10 127)) <<< 23) ||| BitVec.zeroExtend 32 (s.a_m >>> 3)


      if (a_e_is_128 && a_m_neq_0) || (b_e_is_128 && b_m_neq_0) then
        { s with state := FsmState.OUT_RDY, z := nan_z }
      else if a_e_is_128 then
        { s with state := FsmState.OUT_RDY, z := next_z_a128 }
      else if b_e_is_128 then
        { s with state := FsmState.OUT_RDY, z := next_z_b128 }
      else if (a_e_is_neg127 && a_m_is_0) && (b_e_is_neg127 && b_m_is_0) then
        { s with state := FsmState.OUT_RDY, z := next_z_both_zero }
      else if a_e_is_neg127 && a_m_is_0 then
        { s with state := FsmState.OUT_RDY, z := next_z_a_zero }
      else if b_e_is_neg127 && b_m_is_0 then
        { s with state := FsmState.OUT_RDY, z := next_z_b_zero }
      else
        let next_a_e := if a_e_is_neg127 then (BitVec.ofNat 10 0 - BitVec.ofNat 10 126) else s.a_e
        let next_a_m := if a_e_is_neg127 then s.a_m else s.a_m ||| (BitVec.ofNat 27 1 <<< 26)
        let next_b_e := if b_e_is_neg127 then (BitVec.ofNat 10 0 - BitVec.ofNat 10 126) else s.b_e
        let next_b_m := if b_e_is_neg127 then s.b_m else s.b_m ||| (BitVec.ofNat 27 1 <<< 26)
        { s with state := FsmState.ALIGN, a_e := next_a_e, a_m := next_a_m, b_e := next_b_e, b_m := next_b_m }

    | FsmState.ALIGN =>
      if s.a_e.toInt > s.b_e.toInt then
        let next_b_e := s.b_e + 1
        let b_m_shifted := s.b_m >>> 1
        let bit0 := s.b_m.getLsb 0 || s.b_m.getLsb 1
        let next_b_m := if bit0 then b_m_shifted ||| BitVec.ofNat 27 1 else b_m_shifted &&& ~~~(BitVec.ofNat 27 1)
        { s with b_e := next_b_e, b_m := next_b_m }
      else if s.a_e.toInt < s.b_e.toInt then
        let next_a_e := s.a_e + 1
        let a_m_shifted := s.a_m >>> 1
        let bit0 := s.a_m.getLsb 0 || s.a_m.getLsb 1
        let next_a_m := if bit0 then a_m_shifted ||| BitVec.ofNat 27 1 else a_m_shifted &&& ~~~(BitVec.ofNat 27 1)
        { s with a_e := next_a_e, a_m := next_a_m }
      else
        { s with state := FsmState.ADD_0 }

    | FsmState.ADD_0 =>
      let next_z_e := s.a_e
      if s.a_s == s.b_s then
        let next_pre_sum := (BitVec.zeroExtend 28 s.a_m) + (BitVec.zeroExtend 28 s.b_m)
        { s with state := FsmState.ADD_1, z_e := next_z_e, pre_sum := next_pre_sum, z_s := s.a_s }
      else
        if s.a_m >= s.b_m then
          let next_pre_sum := (BitVec.zeroExtend 28 s.a_m) - (BitVec.zeroExtend 28 s.b_m)
          { s with state := FsmState.ADD_1, z_e := next_z_e, pre_sum := next_pre_sum, z_s := s.a_s }
        else
          let next_pre_sum := (BitVec.zeroExtend 28 s.b_m) - (BitVec.zeroExtend 28 s.a_m)
          { s with state := FsmState.ADD_1, z_e := next_z_e, pre_sum := next_pre_sum, z_s := s.b_s }

    | FsmState.ADD_1 =>
      if s.pre_sum.getLsb 27 then
        let next_z_m := BitVec.zeroExtend 24 (s.pre_sum.extractLsb 27 4)
        let next_guard := s.pre_sum.getLsb 3
        let next_round_bit := s.pre_sum.getLsb 2
        let next_sticky := s.pre_sum.getLsb 1 || s.pre_sum.getLsb 0
        let next_z_e := s.z_e + 1
        { s with state := FsmState.NORMALISE_1, z_m := next_z_m, guard := next_guard, round_bit := next_round_bit, sticky := next_sticky, z_e := next_z_e }
      else
        let next_z_m := BitVec.zeroExtend 24 (s.pre_sum.extractLsb 26 3)
        let next_guard := s.pre_sum.getLsb 2
        let next_round_bit := s.pre_sum.getLsb 1
        let next_sticky := s.pre_sum.getLsb 0
        { s with state := FsmState.NORMALISE_1, z_m := next_z_m, guard := next_guard, round_bit := next_round_bit, sticky := next_sticky }

    | FsmState.NORMALISE_1 =>
      if !s.z_m.getLsb 23 && s.z_e.toInt > -126 then
        let next_z_e := s.z_e - 1
        let next_z_m := (s.z_m <<< 1) ||| (if s.guard then BitVec.ofNat 24 1 else BitVec.ofNat 24 0)
        let next_guard := s.round_bit
        let next_round_bit := false
        { s with z_e := next_z_e, z_m := next_z_m, guard := next_guard, round_bit := next_round_bit }
      else
        { s with state := FsmState.NORMALISE_2 }

    | FsmState.NORMALISE_2 =>
      if s.z_e.toInt < -126 then
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
        let next_z_e := if s.z_m == BitVec.ofNat 24 0xffffff then s.z_e + 1 else s.z_e
        { s with state := FsmState.PACK, z_m := next_z_m, z_e := next_z_e }
      else
        { s with state := FsmState.PACK }

    | FsmState.PACK =>
      let sign_bit_bv := if s.z_s then BitVec.ofNat 32 1 <<< 31 else BitVec.ofNat 32 0
      let exp_add := BitVec.zeroExtend 8 (s.z_e + BitVec.ofNat 10 127)
      let exp_val_bv := (BitVec.zeroExtend 32 exp_add) <<< 23
      let mant_val_bv := BitVec.zeroExtend 32 s.z_m

      let next_z := sign_bit_bv ||| exp_val_bv ||| mant_val_bv

      let next_z2 := if s.z_e.toInt == -126 && !s.z_m.getLsb 23 then
                       next_z &&& ~~~(BitVec.ofNat 32 255 <<< 23)
                     else
                       next_z

      let next_z3 := if s.z_e.toInt == -126 && s.z_m == BitVec.ofNat 24 0 then
                       next_z2 &&& ~~~(BitVec.ofNat 32 1 <<< 31)
                     else
                       next_z2

      let next_z4 := if s.z_e.toInt > 127 then
                       sign_bit_bv ||| (BitVec.ofNat 32 255 <<< 23)
                     else
                       next_z3

      { s with state := FsmState.OUT_RDY, z := next_z4 }

    | FsmState.OUT_RDY =>
      { s with rdy := true, result := s.z, state := FsmState.WAIT_REQ }

def out (s : State) : Output :=
  { result := s.result, rdy := s.rdy }

@[simp] theorem step_reset (s : State) (i : Input) :
  i.rst_n = false → step s i = init := by
  intro h; simp [step, h, init]

end fpu_sp_add
