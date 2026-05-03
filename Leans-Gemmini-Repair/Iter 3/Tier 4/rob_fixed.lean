import Std

namespace ROB

structure RobEntry where
  valid : Bool
  completed : Bool
  arch_rd : BitVec 5
  phys_rd : BitVec 6
  old_phys_rd : BitVec 6
  reg_write : Bool
  mem_write : Bool
  mem_read : Bool
  branch : Bool
  branch_type : BitVec 4
  branch_mispredicted : Bool
  branch_correct_pc : BitVec 32
  pc : BitVec 32
  predicted_target : BitVec 32
  predicted_taken : Bool
  checkpoint_id : BitVec 3
  checkpoint_valid : Bool
  exception : Bool
  result : BitVec 32
deriving Repr, DecidableEq

def initEntry : RobEntry := {
  valid := false, completed := false, arch_rd := 0, phys_rd := 0, old_phys_rd := 0,
  reg_write := false, mem_write := false, mem_read := false, branch := false,
  branch_type := 0, branch_mispredicted := false, branch_correct_pc := 0,
  pc := 0, predicted_target := 0, predicted_taken := false, checkpoint_id := 0,
  checkpoint_valid := false, exception := false, result := 0
}

instance : Inhabited RobEntry := ⟨initEntry⟩

structure State (w_idx : Nat) where
  entries : Array RobEntry
  head_ptr : BitVec (w_idx + 1)
  tail_ptr : BitVec (w_idx + 1)
  count : BitVec (w_idx + 1)
deriving Repr, DecidableEq

def init {w_idx : Nat} : State w_idx := {
  entries := Array.mkArray (2 ^ w_idx) initEntry,
  head_ptr := 0,
  tail_ptr := 0,
  count := 0
}

structure Input (dw cw cdbw w_idx : Nat) where
  rst : Bool
  dispatch_valid : Array Bool
  dispatch_arch_rd : Array (BitVec 5)
  dispatch_phys_rd : Array (BitVec 6)
  dispatch_old_phys_rd : Array (BitVec 6)
  dispatch_reg_write : Array Bool
  dispatch_mem_write : Array Bool
  dispatch_mem_read : Array Bool
  dispatch_branch : Array Bool
  dispatch_branch_type : Array (BitVec 4)
  dispatch_pc : Array (BitVec 32)
  dispatch_predicted_target : Array (BitVec 32)
  dispatch_predicted_taken : Array Bool
  dispatch_checkpoint_id : Array (BitVec 3)
  dispatch_checkpoint_valid : Array Bool

  cdb_valid : Array Bool
  cdb_tag : Array (BitVec 6)
  cdb_data : Array (BitVec 32)
  cdb_rob_idx : Array (BitVec (w_idx + 1))

  cdb_branch_complete : Bool
  cdb_branch_mispredicted : Bool
  cdb_branch_correct_pc : BitVec 32
  cdb_branch_rob_idx : BitVec (w_idx + 1)

  load_complete_valid : Bool
  load_complete_rob_idx : BitVec (w_idx + 1)

  store_addr_valid : Bool
  store_addr_rob_idx : BitVec (w_idx + 1)
deriving Repr, DecidableEq

structure Output (dw cw w_idx : Nat) where
  dispatch_rob_idx : Array (BitVec (w_idx + 1))
  dispatch_rob_valid : Array Bool
  rob_full : Bool

  commit_valid : Array Bool
  commit_arch_rd : Array (BitVec 5)
  commit_phys_rd : Array (BitVec 6)
  commit_old_phys_rd : Array (BitVec 6)
  commit_reg_write : Array Bool
  commit_store : Array Bool
  commit_load : Array Bool
  commit_rob_idx : Array (BitVec (w_idx + 1))
  commit_pc : Array (BitVec 32)

  flush : Bool
  flush_pc : BitVec 32
  flush_rob_idx : BitVec (w_idx + 1)
  flush_checkpoint_id : BitVec 3

  store_commit_valid : Array Bool
  store_commit_rob_idx : Array (BitVec (w_idx + 1))

  rob_count : BitVec (w_idx + 1)
  rob_empty : Bool
  rob_head : BitVec (w_idx + 1)
  rob_tail : BitVec (w_idx + 1)
deriving Repr, DecidableEq

def get_idx {w_idx : Nat} (ptr : BitVec (w_idx + 1)) : BitVec (w_idx + 1) :=
  ptr &&& BitVec.ofNat (w_idx + 1) ((2 ^ w_idx) - 1)

def get_wrap {w_idx : Nat} (ptr : BitVec (w_idx + 1)) : Bool :=
  ptr.getLsb ⟨w_idx, Nat.lt_succ_self w_idx⟩

def arrayGetD {α : Type} (arr : Array α) (idx : Nat) (defVal : α) : α :=
  arr.getD idx defVal

def arraySetD {α : Type} (arr : Array α) (idx : Nat) (val : α) : Array α :=
  arr.set! idx val

def step {dw cw cdbw w_idx : Nat} (s : State w_idx) (i : Input dw cw cdbw w_idx) : State w_idx := Id.run do
  if i.rst then
    return init

  let mut next_entries := s.entries
  let mut next_tail := s.tail_ptr
  let mut next_head := s.head_ptr
  let mut next_count := s.count

  for j in [0:cdbw] do
    if arrayGetD i.cdb_valid j false then
      let idx := arrayGetD i.cdb_rob_idx j 0
      let idx_nat := (get_idx idx).toNat % (2 ^ w_idx)
      let entry := arrayGetD next_entries idx_nat initEntry
      if entry.valid then
        next_entries := arraySetD next_entries idx_nat { entry with completed := true, result := arrayGetD i.cdb_data j 0 }

  if i.cdb_branch_complete then
    let idx_nat := (get_idx i.cdb_branch_rob_idx).toNat % (2 ^ w_idx)
    let entry := arrayGetD next_entries idx_nat initEntry
    if entry.valid && entry.branch then
      next_entries := arraySetD next_entries idx_nat { entry with completed := true, branch_mispredicted := i.cdb_branch_mispredicted, branch_correct_pc := i.cdb_branch_correct_pc }

  if i.load_complete_valid then
    let idx_nat := (get_idx i.load_complete_rob_idx).toNat % (2 ^ w_idx)
    let entry := arrayGetD next_entries idx_nat initEntry
    if entry.valid && entry.mem_read then
      next_entries := arraySetD next_entries idx_nat { entry with completed := true }

  if i.store_addr_valid then
    let idx_nat := (get_idx i.store_addr_rob_idx).toNat % (2 ^ w_idx)
    let entry := arrayGetD next_entries idx_nat initEntry
    if entry.valid && entry.mem_write then
      next_entries := arraySetD next_entries idx_nat { entry with completed := true }

  let mut commit_misprediction := false
  let mut misprediction_rob_idx : BitVec (w_idx + 1) := 0
  let mut commit_count : Nat := 0

  for j in [0:cw] do
    let check_ptr := s.head_ptr + BitVec.ofNat (w_idx + 1) j
    let idx_nat := (get_idx check_ptr).toNat % (2 ^ w_idx)
    let entry := arrayGetD next_entries idx_nat initEntry
    let is_misp := entry.branch && entry.branch_mispredicted
    let can_commit := entry.valid && entry.completed && !commit_misprediction && (check_ptr != s.tail_ptr)
    if can_commit then
      commit_count := commit_count + 1
      if is_misp then
        commit_misprediction := true
        misprediction_rob_idx := check_ptr

  if commit_misprediction then
    next_tail := misprediction_rob_idx + 1
    next_head := s.head_ptr + BitVec.ofNat (w_idx + 1) commit_count
    let head_idx_bv := get_idx s.head_ptr
    let misp_idx_bv := get_idx misprediction_rob_idx
    let mispredict_age := misp_idx_bv - head_idx_bv

    for k in [0:(2 ^ w_idx)] do
      let k_bv := BitVec.ofNat (w_idx + 1) k
      let entry_age := k_bv - head_idx_bv
      if k_bv == misp_idx_bv then
         let entry := arrayGetD next_entries k initEntry
         next_entries := arraySetD next_entries k { entry with valid := false, completed := false }
      else if (arrayGetD next_entries k initEntry).valid then
         if entry_age > mispredict_age then
           let entry := arrayGetD next_entries k initEntry
           next_entries := arraySetD next_entries k { entry with valid := false, completed := false }

    next_count := mispredict_age + 1 - BitVec.ofNat (w_idx + 1) commit_count
  else
    for j in [0:commit_count] do
      let check_ptr := s.head_ptr + BitVec.ofNat (w_idx + 1) j
      let idx_nat := (get_idx check_ptr).toNat % (2 ^ w_idx)
      let entry := arrayGetD next_entries idx_nat initEntry
      next_entries := arraySetD next_entries idx_nat { entry with valid := false, completed := false }

    let mut dispatch_count : Nat := 0
    let mut curr_tail := s.tail_ptr
    for j in [0:dw] do
      let tentative_tail := curr_tail + 1
      let has_space := !((get_idx tentative_tail == get_idx s.head_ptr) &&
                         (get_wrap tentative_tail != get_wrap s.head_ptr))
      let can_disp := arrayGetD i.dispatch_valid j false && has_space
      if can_disp then
        let alloc_idx_nat := (get_idx curr_tail).toNat % (2 ^ w_idx)
        let mut new_entry := initEntry
        new_entry := { new_entry with
          valid := true,
          completed := false,
          arch_rd := arrayGetD i.dispatch_arch_rd j 0,
          phys_rd := arrayGetD i.dispatch_phys_rd j 0,
          old_phys_rd := arrayGetD i.dispatch_old_phys_rd j 0,
          reg_write := arrayGetD i.dispatch_reg_write j false,
          mem_write := arrayGetD i.dispatch_mem_write j false,
          mem_read := arrayGetD i.dispatch_mem_read j false,
          branch := arrayGetD i.dispatch_branch j false,
          branch_type := arrayGetD i.dispatch_branch_type j 0,
          pc := arrayGetD i.dispatch_pc j 0,
          predicted_target := arrayGetD i.dispatch_predicted_target j 0,
          predicted_taken := arrayGetD i.dispatch_predicted_taken j false,
          checkpoint_id := arrayGetD i.dispatch_checkpoint_id j 0,
          checkpoint_valid := arrayGetD i.dispatch_checkpoint_valid j false
        }
        next_entries := arraySetD next_entries alloc_idx_nat new_entry
        curr_tail := tentative_tail
        dispatch_count := dispatch_count + 1

    next_tail := curr_tail
    next_head := s.head_ptr + BitVec.ofNat (w_idx + 1) commit_count
    next_count := s.count + BitVec.ofNat (w_idx + 1) dispatch_count - BitVec.ofNat (w_idx + 1) commit_count

  return { entries := next_entries, head_ptr := next_head, tail_ptr := next_tail, count := next_count }

def out {dw cw cdbw w_idx : Nat} (s : State w_idx) (i : Input dw cw cdbw w_idx) : Output dw cw w_idx := Id.run do
  let mut out_dispatch_rob_idx := Array.mkArray dw (BitVec.ofNat (w_idx + 1) 0)
  let mut out_dispatch_rob_valid := Array.mkArray dw false
  let mut curr_tail := s.tail_ptr

  for j in [0:dw] do
    let tentative_tail := curr_tail + 1
    let has_space := !((get_idx tentative_tail == get_idx s.head_ptr) &&
                       (get_wrap tentative_tail != get_wrap s.head_ptr))
    let can_disp := arrayGetD i.dispatch_valid j false && has_space
    if can_disp then
      out_dispatch_rob_idx := arraySetD out_dispatch_rob_idx j (get_idx curr_tail)
      out_dispatch_rob_valid := arraySetD out_dispatch_rob_valid j true
      curr_tail := tentative_tail

  let mut out_commit_valid := Array.mkArray cw false
  let mut out_commit_arch_rd := Array.mkArray cw (BitVec.ofNat 5 0)
  let mut out_commit_phys_rd := Array.mkArray cw (BitVec.ofNat 6 0)
  let mut out_commit_old_phys_rd := Array.mkArray cw (BitVec.ofNat 6 0)
  let mut out_commit_reg_write := Array.mkArray cw false
  let mut out_commit_store := Array.mkArray cw false
  let mut out_commit_load := Array.mkArray cw false
  let mut out_commit_rob_idx := Array.mkArray cw (BitVec.ofNat (w_idx + 1) 0)
  let mut out_commit_pc := Array.mkArray cw (BitVec.ofNat 32 0)

  let mut out_store_commit_valid := Array.mkArray cw false
  let mut out_store_commit_rob_idx := Array.mkArray cw (BitVec.ofNat (w_idx + 1) 0)

  let mut commit_misprediction := false
  let mut misprediction_rob_idx : BitVec (w_idx + 1) := 0
  let mut misprediction_correct_pc : BitVec 32 := 0
  let mut misprediction_checkpoint_id : BitVec 3 := 0

  for j in [0:cw] do
    let check_ptr := s.head_ptr + BitVec.ofNat (w_idx + 1) j
    let idx_nat := (get_idx check_ptr).toNat % (2 ^ w_idx)
    let entry := arrayGetD s.entries idx_nat initEntry
    let is_misp := entry.branch && entry.branch_mispredicted
    let can_commit := entry.valid && entry.completed && !commit_misprediction && (check_ptr != s.tail_ptr)

    if can_commit then
      out_commit_valid := arraySetD out_commit_valid j true
      out_commit_arch_rd := arraySetD out_commit_arch_rd j entry.arch_rd
      out_commit_phys_rd := arraySetD out_commit_phys_rd j entry.phys_rd
      out_commit_old_phys_rd := arraySetD out_commit_old_phys_rd j entry.old_phys_rd
      out_commit_reg_write := arraySetD out_commit_reg_write j entry.reg_write
      out_commit_store := arraySetD out_commit_store j entry.mem_write
      out_commit_load := arraySetD out_commit_load j entry.mem_read
      out_commit_rob_idx := arraySetD out_commit_rob_idx j (get_idx check_ptr)
      out_commit_pc := arraySetD out_commit_pc j entry.pc

      out_store_commit_valid := arraySetD out_store_commit_valid j entry.mem_write
      out_store_commit_rob_idx := arraySetD out_store_commit_rob_idx j (get_idx check_ptr)

      if is_misp then
        commit_misprediction := true
        misprediction_rob_idx := get_idx check_ptr
        misprediction_correct_pc := entry.branch_correct_pc
        misprediction_checkpoint_id := entry.checkpoint_id

  let rob_empty := (get_idx s.head_ptr == get_idx s.tail_ptr) && (get_wrap s.head_ptr == get_wrap s.tail_ptr)
  let rob_full := (get_idx s.head_ptr == get_idx s.tail_ptr) && (get_wrap s.head_ptr != get_wrap s.tail_ptr)

  return {
    dispatch_rob_idx := out_dispatch_rob_idx,
    dispatch_rob_valid := out_dispatch_rob_valid,
    rob_full := rob_full,

    commit_valid := out_commit_valid,
    commit_arch_rd := out_commit_arch_rd,
    commit_phys_rd := out_commit_phys_rd,
    commit_old_phys_rd := out_commit_old_phys_rd,
    commit_reg_write := out_commit_reg_write,
    commit_store := out_commit_store,
    commit_load := out_commit_load,
    commit_rob_idx := out_commit_rob_idx,
    commit_pc := out_commit_pc,

    flush := commit_misprediction,
    flush_pc := misprediction_correct_pc,
    flush_rob_idx := misprediction_rob_idx,
    flush_checkpoint_id := misprediction_checkpoint_id,

    store_commit_valid := out_store_commit_valid,
    store_commit_rob_idx := out_store_commit_rob_idx,

    rob_count := s.count,
    rob_empty := rob_empty,
    rob_head := get_idx s.head_ptr,
    rob_tail := get_idx s.tail_ptr
  }

@[simp] theorem step_reset {dw cw cdbw w_idx : Nat} (s : State w_idx) (i : Input dw cw cdbw w_idx) :
  i.rst = true → step s i = init := by
  intro h
  simp [step, h, init]

end ROB
