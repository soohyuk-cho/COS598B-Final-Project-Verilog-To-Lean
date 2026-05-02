import Std

namespace async_shift_register_fifo

structure State (w a : Nat) where
  fifo_mem : List (BitVec w)
  data_out : BitVec w
  wr_ptr_bin : BitVec (a + 1)
  wr_ptr_gray : BitVec (a + 1)
  rd_ptr_bin : BitVec (a + 1)
  rd_ptr_gray : BitVec (a + 1)
  wr_ptr_gray_sync1 : BitVec (a + 1)
  wr_ptr_gray_sync2 : BitVec (a + 1)
  rd_ptr_gray_sync1 : BitVec (a + 1)
  rd_ptr_gray_sync2 : BitVec (a + 1)
deriving Repr, DecidableEq

structure Input (w : Nat) where
  rst : Bool
  write_en : Bool
  read_en : Bool
  data_in : BitVec w
deriving Repr, DecidableEq

structure Output (w : Nat) where
  data_out : BitVec w
  full : Bool
  empty : Bool
deriving Repr, DecidableEq

def init {w a : Nat} : State w a := {
  fifo_mem := List.replicate (2 ^ a) (BitVec.ofNat w 0)
  data_out := BitVec.ofNat w 0
  wr_ptr_bin := BitVec.ofNat (a + 1) 0
  wr_ptr_gray := BitVec.ofNat (a + 1) 0
  rd_ptr_bin := BitVec.ofNat (a + 1) 0
  rd_ptr_gray := BitVec.ofNat (a + 1) 0
  wr_ptr_gray_sync1 := BitVec.ofNat (a + 1) 0
  wr_ptr_gray_sync2 := BitVec.ofNat (a + 1) 0
  rd_ptr_gray_sync1 := BitVec.ofNat (a + 1) 0
  rd_ptr_gray_sync2 := BitVec.ofNat (a + 1) 0
}

def step {w a : Nat} (s : State w a) (i : Input w) : State w a :=
  if i.rst then
    init
  else
    let target_full := s.rd_ptr_gray_sync2 ^^^ (BitVec.ofNat (a + 1) (3 <<< (a - 1)))
    let full := s.wr_ptr_gray == target_full
    let target_empty := s.wr_ptr_gray_sync2
    let empty := s.rd_ptr_gray == target_empty

    let we := i.write_en && !full
    let re := i.read_en && !empty

    let wr_ptr_bin_next := s.wr_ptr_bin + (if we then 1 else 0)
    let wr_ptr_gray_next := (wr_ptr_bin_next >>> 1) ^^^ wr_ptr_bin_next

    let rd_ptr_bin_next := s.rd_ptr_bin + (if re then 1 else 0)
    let rd_ptr_gray_next := (rd_ptr_bin_next >>> 1) ^^^ rd_ptr_bin_next

    let mask : Nat := (1 <<< a) - 1

    let idx_wr := (s.wr_ptr_bin &&& BitVec.ofNat (a + 1) mask).toNat
    let next_mem := if we then s.fifo_mem.set idx_wr i.data_in else s.fifo_mem

    let idx_rd := (s.rd_ptr_bin &&& BitVec.ofNat (a + 1) mask).toNat
    let next_data_out := if re then s.fifo_mem.getD idx_rd (BitVec.ofNat w 0) else s.data_out

    { fifo_mem := next_mem
    , data_out := next_data_out
    , wr_ptr_bin := wr_ptr_bin_next
    , wr_ptr_gray := wr_ptr_gray_next
    , rd_ptr_bin := rd_ptr_bin_next
    , rd_ptr_gray := rd_ptr_gray_next
    , wr_ptr_gray_sync1 := s.wr_ptr_gray
    , wr_ptr_gray_sync2 := s.wr_ptr_gray_sync1
    , rd_ptr_gray_sync1 := s.rd_ptr_gray
    , rd_ptr_gray_sync2 := s.rd_ptr_gray_sync1 }

def out {w a : Nat} (s : State w a) : Output w :=
  let target_full := s.rd_ptr_gray_sync2 ^^^ (BitVec.ofNat (a + 1) (3 <<< (a - 1)))
  let target_empty := s.wr_ptr_gray_sync2
  { data_out := s.data_out
  , full := s.wr_ptr_gray == target_full
  , empty := s.rd_ptr_gray == target_empty }

@[simp] theorem step_reset {w a : Nat} (s : State w a) (we re : Bool) (din : BitVec w) :
  step s { rst := true, write_en := we, read_en := re, data_in := din } = init := by
  simp [step, init]

@[simp] theorem step_hold {w a : Nat} (s : State w a) (din : BitVec w) :
  step s { rst := false, write_en := false, read_en := false, data_in := din } =
  { s with
    wr_ptr_gray := (s.wr_ptr_bin >>> 1) ^^^ s.wr_ptr_bin,
    rd_ptr_gray := (s.rd_ptr_bin >>> 1) ^^^ s.rd_ptr_bin,
    wr_ptr_gray_sync1 := s.wr_ptr_gray,
    wr_ptr_gray_sync2 := s.wr_ptr_gray_sync1,
    rd_ptr_gray_sync1 := s.rd_ptr_gray,
    rd_ptr_gray_sync2 := s.rd_ptr_gray_sync1 } := by
  simp [step]

end async_shift_register_fifo
