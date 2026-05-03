import Std

namespace async_fifo

structure State (d a : Nat) where
  mem              : List (BitVec d)
  rd_data          : BitVec d
  wr_ptr_bin       : BitVec (a + 1)
  wr_ptr_gray      : BitVec (a + 1)
  wr_ptr_gray_sync : BitVec (a + 1)
  rd_ptr_bin       : BitVec (a + 1)
  rd_ptr_gray      : BitVec (a + 1)
  rd_ptr_gray_sync : BitVec (a + 1)
deriving Repr, DecidableEq

structure Input (d : Nat) where
  wr_rst_n : Bool
  rd_rst_n : Bool
  wr_en    : Bool
  rd_en    : Bool
  wr_data  : BitVec d
deriving Repr, DecidableEq

structure Output (d : Nat) where
  rd_data : BitVec d
  full    : Bool
  empty   : Bool
deriving Repr, DecidableEq

def init {d a : Nat} : State d a :=
  { mem := List.replicate (2 ^ a) (BitVec.ofNat d 0)
  , rd_data := BitVec.ofNat d 0
  , wr_ptr_bin := BitVec.ofNat (a + 1) 0
  , wr_ptr_gray := BitVec.ofNat (a + 1) 0
  , wr_ptr_gray_sync := BitVec.ofNat (a + 1) 0
  , rd_ptr_bin := BitVec.ofNat (a + 1) 0
  , rd_ptr_gray := BitVec.ofNat (a + 1) 0
  , rd_ptr_gray_sync := BitVec.ofNat (a + 1) 0 }

def gray_to_bin_loop {a : Nat} (gray : BitVec (a + 1)) : Nat → BitVec (a + 1) → BitVec (a + 1)
  | 0, acc => acc
  | j + 1, acc =>
    let bit := (acc >>> (j + 1)) ^^^ (gray >>> j)
    let mask := BitVec.ofNat (a + 1) 1 <<< j
    let new_acc := (acc &&& ~~~mask) ||| (bit &&& mask)
    gray_to_bin_loop gray j new_acc

def gray_to_bin {a : Nat} (gray : BitVec (a + 1)) : BitVec (a + 1) :=
  let initial_acc := BitVec.ofNat (a + 1) 0
  let msb_mask := BitVec.ofNat (a + 1) 1 <<< a
  let start_acc := (gray &&& msb_mask)
  gray_to_bin_loop gray a start_acc

def is_full {a : Nat} (wr_ptr_gray rd_ptr_bin_sync : BitVec (a + 1)) : Bool :=
  let mask := BitVec.ofNat (a + 1) ((1 <<< a) - 1)
  let lower_bits := rd_ptr_bin_sync &&& mask
  let msb_inv := !(rd_ptr_bin_sync.getLsb ⟨a, Nat.lt_succ_self a⟩)
  let upper_bit := if msb_inv then BitVec.ofNat (a + 1) (1 <<< a) else BitVec.ofNat (a + 1) 0
  wr_ptr_gray == (upper_bit ||| lower_bits)

def step {d a : Nat} (s : State d a) (i : Input d) : State d a :=
  let wr_ptr_bin_sync := gray_to_bin s.wr_ptr_gray_sync
  let rd_ptr_bin_sync := gray_to_bin s.rd_ptr_gray_sync
  let full := is_full s.wr_ptr_gray rd_ptr_bin_sync
  let empty := (wr_ptr_bin_sync == s.rd_ptr_gray)

  let (next_rd_ptr_gray_sync, next_wr_ptr_bin, next_wr_ptr_gray, next_mem) :=
    if !i.wr_rst_n then
      (BitVec.ofNat (a + 1) 0, BitVec.ofNat (a + 1) 0, BitVec.ofNat (a + 1) 0, s.mem)
    else
      let r_sync := s.rd_ptr_gray
      if i.wr_en && !full then
        let w_bin := s.wr_ptr_bin + 1
        let w_gray := w_bin ^^^ (w_bin >>> 1)
        let idx := (s.wr_ptr_bin &&& BitVec.ofNat (a + 1) ((1 <<< a) - 1)).toNat
        let m := s.mem.set idx i.wr_data
        (r_sync, w_bin, w_gray, m)
      else
        (r_sync, s.wr_ptr_bin, s.wr_ptr_gray, s.mem)

  let (next_wr_ptr_gray_sync, next_rd_ptr_bin, next_rd_ptr_gray, next_rd_data) :=
    if !i.rd_rst_n then
      (BitVec.ofNat (a + 1) 0, BitVec.ofNat (a + 1) 0, BitVec.ofNat (a + 1) 0, BitVec.ofNat d 0)
    else
      let w_sync := s.wr_ptr_gray
      if i.rd_en && !empty then
        let r_bin := s.rd_ptr_bin + 1
        let r_gray := r_bin ^^^ (r_bin >>> 1)
        let idx := (s.rd_ptr_bin &&& BitVec.ofNat (a + 1) ((1 <<< a) - 1)).toNat
        let r_data := s.mem.getD idx (BitVec.ofNat d 0)
        (w_sync, r_bin, r_gray, r_data)
      else
        (w_sync, s.rd_ptr_bin, s.rd_ptr_gray, s.rd_data)

  { mem := next_mem
  , rd_data := next_rd_data
  , wr_ptr_bin := next_wr_ptr_bin
  , wr_ptr_gray := next_wr_ptr_gray
  , wr_ptr_gray_sync := next_wr_ptr_gray_sync
  , rd_ptr_bin := next_rd_ptr_bin
  , rd_ptr_gray := next_rd_ptr_gray
  , rd_ptr_gray_sync := next_rd_ptr_gray_sync }

def out {d a : Nat} (s : State d a) : Output d :=
  let wr_ptr_bin_sync := gray_to_bin s.wr_ptr_gray_sync
  let rd_ptr_bin_sync := gray_to_bin s.rd_ptr_gray_sync
  let full := is_full s.wr_ptr_gray rd_ptr_bin_sync
  let empty := (wr_ptr_bin_sync == s.rd_ptr_gray)
  { rd_data := s.rd_data
  , full := full
  , empty := empty }

@[simp] theorem step_reset {d a : Nat} (s : State d a) (w_en r_en : Bool) (w_d : BitVec d) :
  step s { wr_rst_n := false, rd_rst_n := false, wr_en := w_en, rd_en := r_en, wr_data := w_d } =
  { s with
    rd_data := BitVec.ofNat d 0,
    wr_ptr_bin := BitVec.ofNat (a + 1) 0,
    wr_ptr_gray := BitVec.ofNat (a + 1) 0,
    wr_ptr_gray_sync := BitVec.ofNat (a + 1) 0,
    rd_ptr_bin := BitVec.ofNat (a + 1) 0,
    rd_ptr_gray := BitVec.ofNat (a + 1) 0,
    rd_ptr_gray_sync := BitVec.ofNat (a + 1) 0 } := by
  simp [step]

@[simp] theorem step_hold {d a : Nat} (s : State d a) (w_d : BitVec d) :
  step s { wr_rst_n := true, rd_rst_n := true, wr_en := false, rd_en := false, wr_data := w_d } =
  { s with
    wr_ptr_gray_sync := s.wr_ptr_gray,
    rd_ptr_gray_sync := s.rd_ptr_gray } := by
  simp [step]

end async_fifo
