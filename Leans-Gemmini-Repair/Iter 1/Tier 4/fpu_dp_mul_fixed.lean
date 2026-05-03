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
      [cite_start]let next_a_m := BitVec.zeroExtend 53 (s.a.extractLsb 51 0) [cite: 1735, 1736]
      [cite_start]let next_b_m := BitVec.zeroExtend 53 (s.b.extractLsb 51 0) [cite: 1736]
      [cite_start]let next_a_e := BitVec.zeroExtend 13 (s.a.extractLsb 62 52) - BitVec.ofNat 13 1023 [cite: 1736]
      [cite_start]let next_b_e := BitVec.zeroExtend 13 (s.b.extractLsb 62 52) - BitVec.ofNat 13 1023 [cite: 1736]
      [cite_start]let next_a_s := s.a.getLsb 63 [cite: 1737]
      [cite_start]let next_b_s := s.b.getLsb 63 [cite: 1737]
      [cite_start]{ s with state := FsmState.SPECIAL_CASES, a_m := next_a_m, b_m := next_b_m, a_e := next_a_e, b_e := next_b_e, a_s := next_a_s, b_s := next_b_s } [cite: 1737]

    | FsmState.SPECIAL_CASES =>
      [cite_start]let a_e_is_1024 := s.a_e == BitVec.ofNat 13 1024 [cite: 1737]
      [cite_start]let b_e_is_1024 := s.b_e == BitVec.ofNat 13 1024 [cite: 1737]
      [cite_start]let a_e_is_neg1023 := s.a_e.toInt == -1023 [cite: 1748]
      [cite_start]let b_e_is_neg1023 := s.b_e.toInt == -1023 [cite: 1750]
      [cite_start]let a_m_nz := s.a_m != BitVec.ofNat 53 0 [cite: 1737]
      [cite_start]let b_m_nz := s.b_m != BitVec.ofNat 53 0 [cite: 1737]
      [cite_start]let a_m_z := s.a_m == BitVec.ofNat 53 0 [cite: 1746]
      [cite_start]let b_m_z := s.b_m == BitVec.ofNat 53 0 [cite: 1740, 1747]

      [cite_start]let nan_z := (BitVec.ofNat 64 0).setBit 63 |>.setLsb 62 52 (BitVec.ofNat 11 2047) |>.setBit 51 [cite: 1737, 1738]

      if (a_e_is_1024 && a_m_nz) || (b_e_is_1024 && b_m_nz) then
        [cite_start]{ s with state := FsmState.OUT_RDY, z := nan_z } [cite: 1737]
      else if a_e_is_1024 then
        [cite_start]let z_inf := (BitVec.ofNat 64 0).setLsb 63 (s.a_s != s.b_s) |>.setLsb 62 52 (BitVec.ofNat 11 2047) [cite: 1739, 1740]
        [cite_start]let z_final := if b_e_is_neg1023 && b_m_z then nan_z else z_inf [cite: 1740, 1741]
        [cite_start]{ s with state := FsmState.OUT_RDY, z := z_final } [cite: 1740]
      else if b_e_is_1024 then
        [cite_start]let z_inf := (BitVec.ofNat 64 0).setLsb 63 (s.a_s != s.b_s) |>.setLsb 62 52 (BitVec.ofNat 11 2047) [cite: 1742, 1743]
        [cite_start]let z_final := if a_e_is_neg1023 && a_m_z then nan_z else z_inf [cite: 1743, 1744]
        [cite_start]{ s with state := FsmState.OUT_RDY, z := z_final } [cite: 1745]
      else if a_e_is_neg1023 && a_m_z then
        [cite_start]let z_zero := (BitVec.ofNat 64 0).setLsb 63 (s.a_s != s.b_s) |>.setLsb 62 52 (BitVec.ofNat 11 0) [cite: 1746, 1747]
        [cite_start]{ s with state := FsmState.OUT_RDY, z := z_zero } [cite: 1747]
      else if b_e_is_neg1023 && b_m_z then
        [cite_start]let z_zero := (BitVec.ofNat 64 0).setLsb 63 (s.a_s != s.b_s) |>.setLsb 62 52 (BitVec.ofNat 11 0) [cite: 1747, 1748]
        [cite_start]{ s with state := FsmState.OUT_RDY, z := z_zero } [cite: 1748]
      else
        [cite_start]let next_a_e := if a_e_is_neg1023 then (BitVec.ofNat 13 0 - BitVec.ofNat 13 1022) else s.a_e [cite: 1748, 1749]
        [cite_start]let next_a_m := if a_e_is_neg1023 then s.a_m else s.a_m.setBit 52 [cite: 1749, 1750]
        [cite_start]let next_b_e := if b_e_is_neg1023 then (BitVec.ofNat 13 0 - BitVec.ofNat 13 1022) else s.b_e [cite: 1750, 1751]
        [cite_start]let next_b_m := if b_e_is_neg1023 then s.b_m else s.b_m.setBit 52 [cite: 1751, 1752]
        [cite_start]{ s with state := FsmState.NORMALISE_A, a_e := next_a_e, a_m := next_a_m, b_e := next_b_e, b_m := next_b_m } [cite: 1753]

    | FsmState.NORMALISE_A =>
      if s.a_m.getLsb 52 then
        [cite_start]{ s with state := FsmState.NORMALISE_B } [cite: 1753, 1754]
      else
        [cite_start]{ s with a_m := s.a_m <<< 1, a_e := s.a_e - 1 } [cite: 1754, 1755]

    | FsmState.NORMALISE_B =>
      if s.b_m.getLsb 52 then
        [cite_start]{ s with state := FsmState.MULTIPLY_0 } [cite: 1755, 1756]
      else
        [cite_start]{ s with b_m := s.b_m <<< 1, b_e := s.b_e - 1 } [cite: 1756, 1757]

    | FsmState.MULTIPLY_0 =>
      [cite_start]let next_z_s := s.a_s != s.b_s [cite: 1758]
      [cite_start]let next_z_e := s.a_e + s.b_e + 1 [cite: 1758]
      [cite_start]let next_product := BitVec.zeroExtend 106 s.a_m * BitVec.zeroExtend 106 s.b_m [cite: 1758]
      [cite_start]{ s with state := FsmState.MULTIPLY_1, z_s := next_z_s, z_e := next_z_e, product := next_product } [cite: 1759]

    | FsmState.MULTIPLY_1 =>
      [cite_start]let next_z_m := BitVec.zeroExtend 53 (s.product.extractLsb 105 53) [cite: 1760]
      [cite_start]let next_guard := s.product.getLsb 52 [cite: 1760]
      [cite_start]let next_round_bit := s.product.getLsb 51 [cite: 1760]
      [cite_start]let next_sticky := BitVec.zeroExtend 51 (s.product.extractLsb 50 0) != BitVec.ofNat 51 0 [cite: 1760]
      [cite_start]{ s with state := FsmState.NORMALISE_1, z_m := next_z_m, guard := next_guard, round_bit := next_round_bit, sticky := next_sticky } [cite: 1761]

    | FsmState.NORMALISE_1 =>
      if !s.z_m.getLsb 52 then
        [cite_start]let next_z_e := s.z_e - 1 [cite: 1761, 1762]
        let next_z_m := (s.z_m <<< 1) | (if s.guard then BitVec.ofNat 53 1 else BitVec.ofNat 53 0) [cite_start][cite: 1762, 1763]
        [cite_start]let next_guard := s.round_bit [cite: 1763]
        [cite_start]let next_round_bit := false [cite: 1763]
        [cite_start]{ s with z_e := next_z_e, z_m := next_z_m, guard := next_guard, round_bit := next_round_bit } [cite: 1763]
      else
        [cite_start]{ s with state := FsmState.NORMALISE_2 } [cite: 1764]

    | FsmState.NORMALISE_2 =>
      if s.z_e.toInt < -1022 then
        [cite_start]let next_z_e := s.z_e + 1 [cite: 1764, 1765]
        [cite_start]let next_z_m := s.z_m >>> 1 [cite: 1765]
        [cite_start]let next_guard := s.z_m.getLsb 0 [cite: 1765]
        [cite_start]let next_round_bit := next_guard [cite: 1765]
        [cite_start]let next_sticky := s.sticky || s.round_bit [cite: 1765, 1766]
        [cite_start]{ s with z_e := next_z_e, z_m := next_z_m, guard := next_guard, round_bit := next_round_bit, sticky := next_sticky } [cite: 1766]
      else
        [cite_start]{ s with state := FsmState.ROUND } [cite: 1767]

    | FsmState.ROUND =>
      if s.guard && (s.round_bit || s.sticky || s.z_m.getLsb 0) then
        [cite_start]let next_z_m := s.z_m + 1 [cite: 1767, 1768]
        [cite_start]let next_z_e := if s.z_m == BitVec.ofNat 53 0x1fffffffffffff then s.z_e + 1 else s.z_e [cite: 1768, 1769]
        [cite_start]{ s with state := FsmState.PACK, z_m := next_z_m, z_e := next_z_e } [cite: 1770]
      else
        [cite_start]{ s with state := FsmState.PACK } [cite: 1770]

    | FsmState.PACK =>
      [cite_start]let mut next_z := BitVec.ofNat 64 0 [cite: 1771]
      [cite_start]next_z := next_z.setBit 63 s.z_s [cite: 1771]
      [cite_start]next_z := next_z.setLsb 62 52 (BitVec.zeroExtend 11 (BitVec.zeroExtend 12 (s.z_e.extractLsb 11 0) + BitVec.ofNat 12 1023).extractLsb 10 0) [cite: 1771]
      [cite_start]next_z := next_z.setLsb 51 0 (BitVec.zeroExtend 52 (s.z_m.extractLsb 51 0)) [cite: 1771]

      if s.z_e.toInt == -1022 && !s.z_m.getLsb 52 then
        [cite_start]next_z := next_z.setLsb 62 52 (BitVec.ofNat 11 0) [cite: 1772, 1773]

      if s.z_e.toInt > 1023 then
        [cite_start]next_z := next_z.setLsb 51 0 (BitVec.ofNat 52 0) |>.setLsb 62 52 (BitVec.ofNat 11 2047) |>.setBit 63 s.z_s [cite: 1774]

      [cite_start]{ s with state := FsmState.OUT_RDY, z := next_z } [cite: 1775]

    | FsmState.OUT_RDY =>
      [cite_start]{ s with rdy := true, result := s.z, state := FsmState.WAIT_REQ } [cite: 1776, 1777]

def out (s : State) : Output :=
  { result := s.result, rdy := s.rdy }

end fpu_dp_mul
