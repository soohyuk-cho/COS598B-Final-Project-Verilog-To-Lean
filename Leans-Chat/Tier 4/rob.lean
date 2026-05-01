import Std

namespace ROB

def ROB_ENTRIES : Nat := 64
def NUM_PHYS_REGS : Nat := 64
def DISPATCH_WIDTH : Nat := 4
def COMMIT_WIDTH : Nat := 4
def CDB_WIDTH : Nat := 4
def ROB_IDX_BITS : Nat := 6
def PTR_BITS : Nat := 7
def PTR_MOD : Nat := 128

abbrev Bit := Bool
abbrev Bits2 := BitVec 2
abbrev Bits3 := BitVec 3
abbrev Bits4 := BitVec 4
abbrev Bits5 := BitVec 5
abbrev Bits6 := BitVec 6
abbrev Bits7 := BitVec 7
abbrev Bits32 := BitVec 32

def bv2 (n : Nat) : Bits2 := BitVec.ofNat 2 n
def bv3 (n : Nat) : Bits3 := BitVec.ofNat 3 n
def bv4 (n : Nat) : Bits4 := BitVec.ofNat 4 n
def bv5 (n : Nat) : Bits5 := BitVec.ofNat 5 n
def bv6 (n : Nat) : Bits6 := BitVec.ofNat 6 n
def bv7 (n : Nat) : Bits7 := BitVec.ofNat 7 n
def bv32 (n : Nat) : Bits32 := BitVec.ofNat 32 n

def BRANCH_TYPE_NONE : Bits4 := bv4 0
def BRANCH_TYPE_J : Bits4 := bv4 1
def BRANCH_TYPE_JAL : Bits4 := bv4 2
def BRANCH_TYPE_JR : Bits4 := bv4 3
def BRANCH_TYPE_BEQ : Bits4 := bv4 4
def BRANCH_TYPE_BNE : Bits4 := bv4 5
def BRANCH_TYPE_BGEZ : Bits4 := bv4 6
def BRANCH_TYPE_BLTZ : Bits4 := bv4 7

def BTB_TYPE_COND : Bits2 := bv2 0
def BTB_TYPE_JUMP : Bits2 := bv2 1
def BTB_TYPE_CALL : Bits2 := bv2 2
def BTB_TYPE_RETURN : Bits2 := bv2 3

structure RobEntry where
  valid : Bit
  completed : Bit
  arch_rd : Bits5
  phys_rd : Bits6
  old_phys_rd : Bits6
  reg_write : Bit
  mem_write : Bit
  mem_read : Bit
  branch : Bit
  branch_type : Bits4
  branch_mispredicted : Bit
  branch_correct_pc : Bits32
  pc : Bits32
  predicted_target : Bits32
  predicted_taken : Bit
  checkpoint_id : Bits3
  checkpoint_valid : Bit
  exception : Bit
  result : Bits32
deriving Repr, DecidableEq, Inhabited

structure State where
  entries : Array RobEntry
  head_ptr : Bits7
  tail_ptr : Bits7
  count : Bits7
deriving Repr, DecidableEq, Inhabited

structure Input where
  rst : Bit
  dispatch_valid : Array Bit
  dispatch_arch_rd : Array Bits5
  dispatch_phys_rd : Array Bits6
  dispatch_old_phys_rd : Array Bits6
  dispatch_reg_write : Array Bit
  dispatch_mem_write : Array Bit
  dispatch_mem_read : Array Bit
  dispatch_branch : Array Bit
  dispatch_branch_type : Array Bits4
  dispatch_pc : Array Bits32
  dispatch_predicted_target : Array Bits32
  dispatch_predicted_taken : Array Bit
  dispatch_checkpoint_id : Array Bits3
  dispatch_checkpoint_valid : Array Bit
  cdb_valid : Array Bit
  cdb_tag : Array Bits6
  cdb_data : Array Bits32
  cdb_rob_idx : Array Bits7
  cdb_branch_complete : Bit
  cdb_branch_mispredicted : Bit
  cdb_branch_correct_pc : Bits32
  cdb_branch_rob_idx : Bits7
  load_complete_valid : Bit
  load_complete_rob_idx : Bits7
  store_addr_valid : Bit
  store_addr_rob_idx : Bits7
deriving Repr, DecidableEq, Inhabited

structure Output where
  dispatch_rob_idx : Array Bits7
  dispatch_rob_valid : Array Bit
  rob_full : Bit
  commit_valid : Array Bit
  commit_arch_rd : Array Bits5
  commit_phys_rd : Array Bits6
  commit_old_phys_rd : Array Bits6
  commit_reg_write : Array Bit
  commit_store : Array Bit
  commit_load : Array Bit
  commit_rob_idx : Array Bits7
  commit_pc : Array Bits32
  flush : Bit
  flush_pc : Bits32
  flush_rob_idx : Bits7
  flush_checkpoint_id : Bits3
  store_commit_valid : Array Bit
  store_commit_rob_idx : Array Bits7
  rob_count : Bits7
  rob_empty : Bit
  rob_head : Bits7
  rob_tail : Bits7
deriving Repr, DecidableEq, Inhabited

def zeroBitsArray (n w : Nat) : Array (BitVec w) :=
  Array.replicate n (BitVec.ofNat w 0)

def zeroBoolArray (n : Nat) : Array Bit :=
  Array.replicate n false

def getA {α : Type} [Inhabited α] (a : Array α) (idx : Nat) : α :=
  a.getD idx default

def emptyEntry : RobEntry :=
  { valid := false
    completed := false
    arch_rd := bv5 0
    phys_rd := bv6 0
    old_phys_rd := bv6 0
    reg_write := false
    mem_write := false
    mem_read := false
    branch := false
    branch_type := bv4 0
    branch_mispredicted := false
    branch_correct_pc := bv32 0
    pc := bv32 0
    predicted_target := bv32 0
    predicted_taken := false
    checkpoint_id := bv3 0
    checkpoint_valid := false
    exception := false
    result := bv32 0 }

def init : State :=
  { entries := Array.replicate ROB_ENTRIES emptyEntry
    head_ptr := bv7 0
    tail_ptr := bv7 0
    count := bv7 0 }

def zeroInput : Input :=
  { rst := false
    dispatch_valid := zeroBoolArray DISPATCH_WIDTH
    dispatch_arch_rd := zeroBitsArray DISPATCH_WIDTH 5
    dispatch_phys_rd := zeroBitsArray DISPATCH_WIDTH 6
    dispatch_old_phys_rd := zeroBitsArray DISPATCH_WIDTH 6
    dispatch_reg_write := zeroBoolArray DISPATCH_WIDTH
    dispatch_mem_write := zeroBoolArray DISPATCH_WIDTH
    dispatch_mem_read := zeroBoolArray DISPATCH_WIDTH
    dispatch_branch := zeroBoolArray DISPATCH_WIDTH
    dispatch_branch_type := zeroBitsArray DISPATCH_WIDTH 4
    dispatch_pc := zeroBitsArray DISPATCH_WIDTH 32
    dispatch_predicted_target := zeroBitsArray DISPATCH_WIDTH 32
    dispatch_predicted_taken := zeroBoolArray DISPATCH_WIDTH
    dispatch_checkpoint_id := zeroBitsArray DISPATCH_WIDTH 3
    dispatch_checkpoint_valid := zeroBoolArray DISPATCH_WIDTH
    cdb_valid := zeroBoolArray CDB_WIDTH
    cdb_tag := zeroBitsArray CDB_WIDTH 6
    cdb_data := zeroBitsArray CDB_WIDTH 32
    cdb_rob_idx := zeroBitsArray CDB_WIDTH 7
    cdb_branch_complete := false
    cdb_branch_mispredicted := false
    cdb_branch_correct_pc := bv32 0
    cdb_branch_rob_idx := bv7 0
    load_complete_valid := false
    load_complete_rob_idx := bv7 0
    store_addr_valid := false
    store_addr_rob_idx := bv7 0 }

def ptrIdx (p : Bits7) : Nat :=
  p.toNat % ROB_ENTRIES

def ptrWrap (p : Bits7) : Nat :=
  (p.toNat / ROB_ENTRIES) % 2

def robIdxFromPtr (p : Bits7) : Bits7 :=
  bv7 (ptrIdx p)

def robEmpty (s : State) : Bit :=
  let ptrMatch := ptrIdx s.head_ptr = ptrIdx s.tail_ptr
  let wrapBitMatch := ptrWrap s.head_ptr = ptrWrap s.tail_ptr
  ptrMatch && wrapBitMatch

def robFull (s : State) : Bit :=
  let ptrMatch := ptrIdx s.head_ptr = ptrIdx s.tail_ptr
  let wrapBitMatch := ptrWrap s.head_ptr = ptrWrap s.tail_ptr
  ptrMatch && !wrapBitMatch

def hasSpaceAfterEnqueue (s : State) (tentativeTail : Bits7) : Bit :=
  !((ptrIdx tentativeTail = ptrIdx s.head_ptr) && (ptrWrap tentativeTail != ptrWrap s.head_ptr))

def mkDispatchEntry (i : Input) (slot : Nat) : RobEntry :=
  { valid := true
    completed := false
    arch_rd := getA i.dispatch_arch_rd slot
    phys_rd := getA i.dispatch_phys_rd slot
    old_phys_rd := getA i.dispatch_old_phys_rd slot
    reg_write := getA i.dispatch_reg_write slot
    mem_write := getA i.dispatch_mem_write slot
    mem_read := getA i.dispatch_mem_read slot
    branch := getA i.dispatch_branch slot
    branch_type := getA i.dispatch_branch_type slot
    branch_mispredicted := false
    branch_correct_pc := bv32 0
    pc := getA i.dispatch_pc slot
    predicted_target := getA i.dispatch_predicted_target slot
    predicted_taken := getA i.dispatch_predicted_taken slot
    checkpoint_id := getA i.dispatch_checkpoint_id slot
    checkpoint_valid := getA i.dispatch_checkpoint_valid slot
    exception := false
    result := bv32 0 }

structure DispatchCalc where
  dispatchRobIdx : Array Bits7
  dispatchRobValid : Array Bit
  nextTail : Bits7
  dispatchCount : Nat
deriving Repr, DecidableEq, Inhabited

def dispatchCalc (s : State) (i : Input) : DispatchCalc :=
  (List.range DISPATCH_WIDTH).foldl
    (fun acc slot =>
      let tentativeTail := acc.nextTail + bv7 1
      let canDispatch := getA i.dispatch_valid slot && hasSpaceAfterEnqueue s tentativeTail
      let nextTail := if canDispatch then acc.nextTail + bv7 1 else acc.nextTail
      let nextCount := if canDispatch then acc.dispatchCount + 1 else acc.dispatchCount
      let ridx := if canDispatch then robIdxFromPtr acc.nextTail else bv7 0
      { dispatchRobIdx := acc.dispatchRobIdx.set! slot ridx
        dispatchRobValid := acc.dispatchRobValid.set! slot canDispatch
        nextTail := nextTail
        dispatchCount := nextCount })
    { dispatchRobIdx := zeroBitsArray DISPATCH_WIDTH 7
      dispatchRobValid := zeroBoolArray DISPATCH_WIDTH
      nextTail := s.tail_ptr
      dispatchCount := 0 }

structure CommitCalc where
  canCommit : Array Bit
  commitValid : Array Bit
  commitArchRd : Array Bits5
  commitPhysRd : Array Bits6
  commitOldPhysRd : Array Bits6
  commitRegWrite : Array Bit
  commitStore : Array Bit
  commitLoad : Array Bit
  commitRobIdx : Array Bits7
  commitPc : Array Bits32
  storeCommitValid : Array Bit
  storeCommitRobIdx : Array Bits7
  nextHead : Bits7
  commitCount : Nat
  commitMisprediction : Bit
  mispredictionRobIdx : Bits7
  mispredictionCorrectPc : Bits32
  mispredictionCheckpointId : Bits3
deriving Repr, DecidableEq, Inhabited

def commitCalc (s : State) : CommitCalc :=
  (List.range COMMIT_WIDTH).foldl
    (fun acc slot =>
      let checkIdx := ptrIdx acc.nextHead
      let entry := getA s.entries checkIdx
      let isMispredictedBranch := entry.branch && entry.branch_mispredicted
      let canCommit :=
        entry.valid && entry.completed && !acc.commitMisprediction && (acc.nextHead != s.tail_ptr)
      if canCommit then
        let ridx := bv7 checkIdx
        { canCommit := acc.canCommit.set! slot true
          commitValid := acc.commitValid.set! slot true
          commitArchRd := acc.commitArchRd.set! slot entry.arch_rd
          commitPhysRd := acc.commitPhysRd.set! slot entry.phys_rd
          commitOldPhysRd := acc.commitOldPhysRd.set! slot entry.old_phys_rd
          commitRegWrite := acc.commitRegWrite.set! slot entry.reg_write
          commitStore := acc.commitStore.set! slot entry.mem_write
          commitLoad := acc.commitLoad.set! slot entry.mem_read
          commitRobIdx := acc.commitRobIdx.set! slot ridx
          commitPc := acc.commitPc.set! slot entry.pc
          storeCommitValid := acc.storeCommitValid.set! slot entry.mem_write
          storeCommitRobIdx := acc.storeCommitRobIdx.set! slot ridx
          nextHead := acc.nextHead + bv7 1
          commitCount := acc.commitCount + 1
          commitMisprediction := acc.commitMisprediction || isMispredictedBranch
          mispredictionRobIdx := if isMispredictedBranch then ridx else acc.mispredictionRobIdx
          mispredictionCorrectPc := if isMispredictedBranch then entry.branch_correct_pc else acc.mispredictionCorrectPc
          mispredictionCheckpointId := if isMispredictedBranch then entry.checkpoint_id else acc.mispredictionCheckpointId }
      else
        acc)
    { canCommit := zeroBoolArray COMMIT_WIDTH
      commitValid := zeroBoolArray COMMIT_WIDTH
      commitArchRd := zeroBitsArray COMMIT_WIDTH 5
      commitPhysRd := zeroBitsArray COMMIT_WIDTH 6
      commitOldPhysRd := zeroBitsArray COMMIT_WIDTH 6
      commitRegWrite := zeroBoolArray COMMIT_WIDTH
      commitStore := zeroBoolArray COMMIT_WIDTH
      commitLoad := zeroBoolArray COMMIT_WIDTH
      commitRobIdx := zeroBitsArray COMMIT_WIDTH 7
      commitPc := zeroBitsArray COMMIT_WIDTH 32
      storeCommitValid := zeroBoolArray COMMIT_WIDTH
      storeCommitRobIdx := zeroBitsArray COMMIT_WIDTH 7
      nextHead := s.head_ptr
      commitCount := 0
      commitMisprediction := false
      mispredictionRobIdx := bv7 0
      mispredictionCorrectPc := bv32 0
      mispredictionCheckpointId := bv3 0 }

def applyDispatch (s : State) (i : Input) (dc : DispatchCalc) : Array RobEntry :=
  (List.range DISPATCH_WIDTH).foldl
    (fun entries slot =>
      if getA dc.dispatchRobValid slot then
        let allocIdx := (getA dc.dispatchRobIdx slot).toNat % ROB_ENTRIES
        entries.set! allocIdx (mkDispatchEntry i slot)
      else
        entries)
    s.entries

def applyCdb (s : State) (i : Input) (entries : Array RobEntry) : Array RobEntry :=
  (List.range CDB_WIDTH).foldl
    (fun es slot =>
      if getA i.cdb_valid slot then
        let completeIdx := (getA i.cdb_rob_idx slot).toNat % ROB_ENTRIES
        let oldEntry := getA s.entries completeIdx
        if oldEntry.valid then
          let curEntry := getA es completeIdx
          es.set! completeIdx { curEntry with completed := true, result := getA i.cdb_data slot }
        else
          es
      else
        es)
    entries

def applyBranchComplete (s : State) (i : Input) (entries : Array RobEntry) : Array RobEntry :=
  if i.cdb_branch_complete then
    let branchIdx := i.cdb_branch_rob_idx.toNat % ROB_ENTRIES
    let oldEntry := getA s.entries branchIdx
    if oldEntry.valid && oldEntry.branch then
      let curEntry := getA entries branchIdx
      entries.set! branchIdx
        { curEntry with
          completed := true
          branch_mispredicted := i.cdb_branch_mispredicted
          branch_correct_pc := i.cdb_branch_correct_pc }
    else
      entries
  else
    entries

def applyLoadComplete (s : State) (i : Input) (entries : Array RobEntry) : Array RobEntry :=
  if i.load_complete_valid then
    let loadIdx := i.load_complete_rob_idx.toNat % ROB_ENTRIES
    let oldEntry := getA s.entries loadIdx
    if oldEntry.valid && oldEntry.mem_read then
      let curEntry := getA entries loadIdx
      entries.set! loadIdx { curEntry with completed := true }
    else
      entries
  else
    entries

def applyStoreAddrReady (s : State) (i : Input) (entries : Array RobEntry) : Array RobEntry :=
  if i.store_addr_valid then
    let storeIdx := i.store_addr_rob_idx.toNat % ROB_ENTRIES
    let oldEntry := getA s.entries storeIdx
    if oldEntry.valid && oldEntry.mem_write then
      let curEntry := getA entries storeIdx
      entries.set! storeIdx { curEntry with completed := true }
    else
      entries
  else
    entries

def applyCommitInvalidation (cc : CommitCalc) (entries : Array RobEntry) : Array RobEntry :=
  (List.range COMMIT_WIDTH).foldl
    (fun es slot =>
      if getA cc.canCommit slot then
        let commitIdx := (getA cc.commitRobIdx slot).toNat % ROB_ENTRIES
        let curEntry := getA es commitIdx
        es.set! commitIdx { curEntry with valid := false, completed := false }
      else
        es)
    entries

def flushEntries (s : State) (cc : CommitCalc) : Array RobEntry :=
  let headIdx := ptrIdx s.head_ptr
  let misIdx := cc.mispredictionRobIdx.toNat % ROB_ENTRIES
  let misAge := (misIdx + PTR_MOD - headIdx) % PTR_MOD
  (List.range ROB_ENTRIES).foldl
    (fun es idx =>
      let oldEntry := getA s.entries idx
      if idx = misIdx then
        let curEntry := getA es idx
        es.set! idx { curEntry with valid := false, completed := false }
      else if oldEntry.valid then
        let entryAge := (idx + PTR_MOD - headIdx) % PTR_MOD
        if entryAge > misAge then
          let curEntry := getA es idx
          es.set! idx { curEntry with valid := false, completed := false }
        else
          es
      else
        es)
    s.entries

def flushedTailPtr (cc : CommitCalc) : Bits7 :=
  bv7 (((cc.mispredictionRobIdx.toNat % ROB_ENTRIES) + 1) % ROB_ENTRIES)

def flushedCount (s : State) (cc : CommitCalc) : Bits7 :=
  let misIdx := cc.mispredictionRobIdx.toNat % ROB_ENTRIES
  let headIdx := ptrIdx s.head_ptr
  bv7 ((((misIdx + ROB_ENTRIES - headIdx) % ROB_ENTRIES) + 1 + PTR_MOD - cc.commitCount) % PTR_MOD)

def evalOutputs (s : State) (i : Input) : Output :=
  let dc := dispatchCalc s i
  let cc := commitCalc s
  { dispatch_rob_idx := dc.dispatchRobIdx
    dispatch_rob_valid := dc.dispatchRobValid
    rob_full := robFull s
    commit_valid := cc.commitValid
    commit_arch_rd := cc.commitArchRd
    commit_phys_rd := cc.commitPhysRd
    commit_old_phys_rd := cc.commitOldPhysRd
    commit_reg_write := cc.commitRegWrite
    commit_store := cc.commitStore
    commit_load := cc.commitLoad
    commit_rob_idx := cc.commitRobIdx
    commit_pc := cc.commitPc
    flush := cc.commitMisprediction
    flush_pc := cc.mispredictionCorrectPc
    flush_rob_idx := cc.mispredictionRobIdx
    flush_checkpoint_id := cc.mispredictionCheckpointId
    store_commit_valid := cc.storeCommitValid
    store_commit_rob_idx := cc.storeCommitRobIdx
    rob_count := s.count
    rob_empty := robEmpty s
    rob_head := bv7 (ptrIdx s.head_ptr)
    rob_tail := bv7 (ptrIdx s.tail_ptr) }

def out (s : State) : Output :=
  evalOutputs s zeroInput

def step (s : State) (i : Input) : State :=
  if i.rst then
    init
  else
    let dc := dispatchCalc s i
    let cc := commitCalc s
    if cc.commitMisprediction then
      { entries := flushEntries s cc
        head_ptr := cc.nextHead
        tail_ptr := flushedTailPtr cc
        count := flushedCount s cc }
    else
      let entries1 := applyDispatch s i dc
      let entries2 := applyCdb s i entries1
      let entries3 := applyBranchComplete s i entries2
      let entries4 := applyLoadComplete s i entries3
      let entries5 := applyStoreAddrReady s i entries4
      let entries6 := applyCommitInvalidation cc entries5
      { entries := entries6
        head_ptr := cc.nextHead
        tail_ptr := dc.nextTail
        count := bv7 ((s.count.toNat + dc.dispatchCount + PTR_MOD - cc.commitCount) % PTR_MOD) }

def singleDispatchInput : Input :=
  { zeroInput with dispatch_valid := #[true, false, false, false] }

def readyEntry0 : RobEntry :=
  { emptyEntry with valid := true, completed := true }

def singleReadyState : State :=
  { entries := (Array.replicate ROB_ENTRIES emptyEntry).set! 0 readyEntry0
    head_ptr := bv7 0
    tail_ptr := bv7 1
    count := bv7 1 }

def mispredictEntry0 : RobEntry :=
  { emptyEntry with
    valid := true
    completed := true
    branch := true
    branch_mispredicted := true
    branch_correct_pc := bv32 42
    checkpoint_id := bv3 3 }

def mispredictState : State :=
  { entries := (Array.replicate ROB_ENTRIES emptyEntry).set! 0 mispredictEntry0
    head_ptr := bv7 0
    tail_ptr := bv7 1
    count := bv7 1 }

@[simp] theorem step_reset (s : State) (i : Input) :
    step s { i with rst := true } = init := by
  simp [step, init]

@[simp] theorem step_hold_empty :
    step init zeroInput = init := by
  native_decide

theorem dispatch_slot0_allocates_idx0 :
    (evalOutputs init singleDispatchInput).dispatch_rob_valid.get! 0 = true := by
  native_decide

theorem step_dispatch_updates_tail :
    (step init singleDispatchInput).tail_ptr = bv7 1 := by
  native_decide

theorem step_dispatch_updates_count :
    (step init singleDispatchInput).count = bv7 1 := by
  native_decide

theorem step_commit_single_advances_head :
    (step singleReadyState zeroInput).head_ptr = bv7 1 := by
  native_decide

theorem step_commit_single_clears_count :
    (step singleReadyState zeroInput).count = bv7 0 := by
  native_decide

theorem flush_detected_on_mispredict :
    (evalOutputs mispredictState zeroInput).flush = true := by
  native_decide

theorem step_flush_redirect_pc :
    (evalOutputs mispredictState zeroInput).flush_pc = bv32 42 := by
  native_decide

end ROB
