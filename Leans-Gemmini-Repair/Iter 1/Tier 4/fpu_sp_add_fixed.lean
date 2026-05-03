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
      [cite_start]let next_a_m := (BitVec.zeroExtend 27 (s.a.extractLsb 22 0)) <<< 3 [cite: 1811]
      [cite_start]let next_b_m := (BitVec.zeroExtend 27 (s.b.extractLsb 22 0)) <<< 3 [cite: 1812]
      [cite_start]let next_a_e := (BitVec.zeroExtend 10 (s.a.extractLsb 30 23)) - BitVec.ofNat 10 127 [cite: 1812]
      [cite_start]let next_b_e := (BitVec.zeroExtend 10 (s.b.extractLsb 30 23)) - BitVec.ofNat 10 127 [cite: 1813]
      [cite_start]let next_a_s := s.a.getLsb 31 [cite: 1813]
      [cite_start]let next_b_s := s.b.getLsb 31 [cite: 1814]
      { s with state := FsmState.SPECIAL_CASES, a_m := next_a_m, b_m := next_b_m, a_e := next_a_e, b_e := next_b_e, a_s := next_a_s, b_s := next_b_s }

    | FsmState.SPECIAL_CASES =>
      [cite_start]let a_e_is_128 := s.a_e == BitVec.ofNat 10 128 [cite: 1814]
      [cite_start]let b_e_is_128 := s.b_e == BitVec.ofNat 10 128 [cite: 1814]
      [cite_start]let a_e_is_neg127 := s.a_e.toInt == -127 [cite: 1821]
      [cite_start]let b_e_is_neg127 := s.b_e.toInt == -127 [cite: 1821]
      [cite_start]let a_m_neq_0 := s.a_m != BitVec.ofNat 27 0 [cite: 1814]
      [cite_start]let b_m_neq_0 := s.b_m != BitVec.ofNat 27 0 [cite: 1814]
      [cite_start]let a_m_is_0 := s.a_m == BitVec.ofNat 27 0 [cite: 1821]
      [cite_start]let b_m_is_0 := s.b_m == BitVec.ofNat 27 0 [cite: 1821]

      if (a_e_is_128 && a_m_neq_0) || (b_e_is_128 && b_m_neq_0) then
        [cite_start]let next_z := (BitVec.ofNat 32 0).setBit 31 |>.setLsb 30 23 (BitVec.ofNat 8 255) |>.setBit 22 [cite: 1814, 1815]
        { s with state := FsmState.OUT_RDY, z := next_z }
      else if a_e_is_128 then
        [cite_start]let next_z_base := (BitVec.ofNat 32 0).setLsb 31 31 (if s.a_s then 1 else 0) |>.setLsb 30 23 (BitVec.ofNat 8 255) [cite: 1816, 1817]
        let next_z := if b_e_is_128 && s.a_s != s.b_s then
                        (BitVec.ofNat 32 0)[cite_start].setLsb 31 31 (if s.b_s then 1 else 0) |>.setLsb 30 23 (BitVec.ofNat 8 255) |>.setBit 22 [cite: 1817, 1818]
                      else next_z_base
        { s with state := FsmState.OUT_RDY, z := next_z }
      else if b_e_is_128 then
        [cite_start]let next_z := (BitVec.ofNat 32 0).setLsb 31 31 (if s.b_s then 1 else 0) |>.setLsb 30 23 (BitVec.ofNat 8 255) [cite: 1819, 1820]
        { s with state := FsmState.OUT_RDY, z := next_z }
      else if (a_e_is_neg127 && a_m_is_0) && (b_e_is_neg127 && b_m_is_0) then
        let next_z := (BitVec.ofNat 32 0).setLsb 31 31 (if s.a_s && s.b_s then 1 else 0)
                      |>.setLsb 30 23 (BitVec.zeroExtend 8 (s.b_e + BitVec.ofNat 10 127))
                      [cite_start]|>.setLsb 22 0 (BitVec.zeroExtend 23 (s.b_m >>> 3)) [cite: 1821]
        { s with state := FsmState.OUT_RDY, z := next_z }
      else if a_e_is_neg127 && a_m_is_0 then
        let next_z := (BitVec.ofNat 32 0).setLsb 31 31 (if s.b_s then 1 else 0)
                      |>.setLsb 30 23 (BitVec.zeroExtend 8 (s.b_e + BitVec.ofNat 10 127))
                      [cite_start]|>.setLsb 22 0 (BitVec.zeroExtend 23 (s.b_m >>> 3)) [cite: 1822, 1823]
        { s with state := FsmState.OUT_RDY, z := next_z }
      else if b_e_is_neg127 && b_m_is_0 then
        let next_z := (BitVec.ofNat 32 0).setLsb 31 31 (if s.a_s then 1 else 0)
                      |>.setLsb 30 23 (BitVec.zeroExtend 8 (s.a_e + BitVec.ofNat 10 127))
                      [cite_start]|>.setLsb 22 0 (BitVec.zeroExtend 23 (s.a_m >>> 3)) [cite: 1824, 1825]
        { s with state := FsmState.OUT_RDY, z := next_z }
      else
        [cite_start]let next_a_e := if a_e_is_neg127 then (BitVec.ofNat 10 0 - BitVec.ofNat 10 126) else s.a_e [cite: 1826, 1827]
        [cite_start]let next_a_m := if a_e_is_neg127 then s.a_m else s.a_m.setBit 26 [cite: 1827, 1828]
        [cite_start]let next_b_e := if b_e_is_neg127 then (BitVec.ofNat 10 0 - BitVec.ofNat 10 126) else s.b_e [cite: 1828, 1829]
        [cite_start]let next_b_m := if b_e_is_neg127 then s.b_m else s.b_m.setBit 26 [cite: 1829, 1830]
        { s with state := FsmState.ALIGN, a_e := next_a_e, a_m := next_a_m, b_e := next_b_e, b_m := next_b_m }

    | FsmState.ALIGN =>
      if s.a_e.toInt > s.b_e.toInt then
        [cite_start]let next_b_e := s.b_e + 1 [cite: 1832]
        [cite_start]let b_m_shifted := s.b_m >>> 1 [cite: 1832]
        [cite_start]let bit0 := s.b_m.getLsb 0 || s.b_m.getLsb 1 [cite: 1833]
        [cite_start]let next_b_m := if bit0 then b_m_shifted.setBit 0 else b_m_shifted [cite: 1833]
        { s with b_e := next_b_e, b_m := next_b_m }
      else if s.a_e.toInt < s.b_e.toInt then
        [cite_start]let next_a_e := s.a_e + 1 [cite: 1834]
        [cite_start]let a_m_shifted := s.a_m >>> 1 [cite: 1834]
        [cite_start]let bit0 := s.a_m.getLsb 0 || s.a_m.getLsb 1 [cite: 1835]
        [cite_start]let next_a_m := if bit0 then a_m_shifted.setBit 0 else a_m_shifted [cite: 1835]
        { s with a_e := next_a_e, a_m := next_a_m }
      else
        { s with state := FsmState.ADD_0 }

    | FsmState.ADD_0 =>
      [cite_start]let next_z_e := s.a_e [cite: 1837]
      if s.a_s == s.b_s then
        [cite_start]let next_pre_sum := (BitVec.zeroExtend 28 s.a_m) + (BitVec.zeroExtend 28 s.b_m) [cite: 1837]
        { s with state := FsmState.ADD_1, z_e := next_z_e, pre_sum := next_pre_sum, z_s := s.a_s }
      else
        if s.a_m >= s.b_m then
          [cite_start]let next_pre_sum := (BitVec.zeroExtend 28 s.a_m) - (BitVec.zeroExtend 28 s.b_m) [cite: 1838, 1839]
          { s with state := FsmState.ADD_1, z_e := next_z_e, pre_sum := next_pre_sum, z_s := s.a_s }
        else
          [cite_start]let next_pre_sum := (BitVec.zeroExtend 28 s.b_m) - (BitVec.zeroExtend 28 s.a_m) [cite: 1839, 1840]
          { s with state := FsmState.ADD_1, z_e := next_z_e, pre_sum := next_pre_sum, z_s := s.b_s }

    | FsmState.ADD_1 =>
      if s.pre_sum.getLsb 27 then
        [cite_start]let next_z_m := BitVec.zeroExtend 24 (s.pre_sum.extractLsb 27 4) [cite: 1842]
        [cite_start]let next_guard := s.pre_sum.getLsb 3 [cite: 1842]
        [cite_start]let next_round_bit := s.pre_sum.getLsb 2 [cite: 1842]
        [cite_start]let next_sticky := s.pre_sum.getLsb 1 || s.pre_sum.getLsb 0 [cite: 1842]
        [cite_start]let next_z_e := s.z_e + 1 [cite: 1842]
        { s with state := FsmState.NORMALISE_1, z_m := next_z_m, guard := next_guard, round_bit := next_round_bit, sticky := next_sticky, z_e := next_z_e }
      else
        [cite_start]let next_z_m := BitVec.zeroExtend 24 (s.pre_sum.extractLsb 26 3) [cite: 1844]
        [cite_start]let next_guard := s.pre_sum.getLsb 2 [cite: 1844]
        [cite_start]let next_round_bit := s.pre_sum.getLsb 1 [cite: 1844]
        [cite_start]let next_sticky := s.pre_sum.getLsb 0 [cite: 1844]
        { s with state := FsmState.NORMALISE_1, z_m := next_z_m, guard := next_guard, round_bit := next_round_bit, sticky := next_sticky }

    | FsmState.NORMALISE_1 =>
      if !s.z_m.getLsb 23 && s.z_e.toInt > -126 then
        [cite_start]let next_z_e := s.z_e - 1 [cite: 1846]
        let next_z_m := (s.z_m <<< 1) | (if s.guard then BitVec.ofNat 24 1 else BitVec.ofNat 24 0) [cite_start][cite: 1846, 1847]
        [cite_start]let next_guard := s.round_bit [cite: 1847]
        [cite_start]let next_round_bit := false [cite: 1847]
        { s with z_e := next_z_e, z_m := next_z_m, guard := next_guard, round_bit := next_round_bit }
      else
        { s with state := FsmState.NORMALISE_2 }

    | FsmState.NORMALISE_2 =>
      if s.z_e.toInt < -126 then
        [cite_start]let next_z_e := s.z_e + 1 [cite: 1849]
        [cite_start]let next_z_m := s.z_m >>> 1 [cite: 1849]
        [cite_start]let next_guard := s.z_m.getLsb 0 [cite: 1849]
        [cite_start]let next_round_bit := next_guard [cite: 1849]
        [cite_start]let next_sticky := s.sticky || s.round_bit [cite: 1850]
        { s with z_e := next_z_e, z_m := next_z_m, guard := next_guard, round_bit := next_round_bit, sticky := next_sticky }
      else
        { s with state := FsmState.ROUND }

    | FsmState.ROUND =>
      if s.guard && (s.round_bit || s.sticky || s.z_m.getLsb 0) then
        [cite_start]let next_z_m := s.z_m + 1 [cite: 1852]
        [cite_start]let next_z_e := if s.z_m == BitVec.ofNat 24 0xffffff then s.z_e + 1 else s.z_e [cite: 1852, 1853]
        { s with state := FsmState.PACK, z_m := next_z_m, z_e := next_z_e }
      else
        { s with state := FsmState.PACK }

    | FsmState.PACK =>
      let mut next_z := BitVec.ofNat 32 0
      [cite_start]next_z := next_z.setBit 31 s.z_s [cite: 1856]
      [cite_start]next_z := next_z.setLsb 30 23 (BitVec.zeroExtend 8 (s.z_e + BitVec.ofNat 10 127)) [cite: 1855]
      [cite_start]next_z := next_z.setLsb 22 0 (BitVec.zeroExtend 23 s.z_m) [cite: 1855]

      if s.z_e.toInt == -126 && !s.z_m.getLsb 23 then
        [cite_start]next_z := next_z.setLsb 30 23 (BitVec.ofNat 8 0) [cite: 1856, 1857]

      if s.z_e.toInt == -126 && s.z_m == BitVec.ofNat 24 0 then
        [cite_start]next_z := next_z.setBit 31 false [cite: 1857, 1858]

      if s.z_e.toInt > 127 then
        [cite_start]next_z := (BitVec.ofNat 32 0).setBit 31 s.z_s |>.setLsb 30 23 (BitVec.ofNat 8 255) [cite: 1859]

      { s with state := FsmState.OUT_RDY, z := next_z }

    | FsmState.OUT_RDY =>
      { s with rdy := true, result := s.z, state := FsmState.WAIT_REQ }

def out (s : State) : Output :=
  { result := s.result, rdy := s.rdy }

end fpu_sp_add
