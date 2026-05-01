import Std

namespace intSqrt

abbrev Bit := Bool
abbrev N : Nat := 32
abbrev SizeOfN : Nat := 32
abbrev CountWidth : Nat := SizeOfN + 1
abbrev Bits := BitVec N
abbrev Count := BitVec CountWidth

inductive CtlState where
  | RESET
  | START
  | RUN
  | DONE
  deriving Repr, DecidableEq

structure State where
  rem : Bits
  sqrt : Bits
  currentBit : Bits
  count : Count
  state : CtlState
  doneReg : Bit
  deriving Repr, DecidableEq

structure Input where
  start : Bit
  in_ : Bits
  deriving Repr, DecidableEq

structure Output where
  out : Bits
  done : Bit
  deriving Repr, DecidableEq

def bv (n : Nat) : Bits := BitVec.ofNat N n
def cv (n : Nat) : Count := BitVec.ofNat CountWidth n

def init : State :=
  { rem := bv 0
    sqrt := bv 0
    currentBit := bv 0
    count := cv 0
    state := CtlState.RESET
    doneReg := false }

def prod (s : State) : Bits :=
  s.sqrt + s.currentBit

def shr1 (x : Bits) : Bits :=
  bv (x.toNat / 2)

def shr2 (x : Bits) : Bits :=
  bv (x.toNat / 4)

def startBit : Bits :=
  bv (if N % 2 = 0 then 2 ^ (N - 2) else 2 ^ (N - 1))

def runLimit : Count :=
  cv (SizeOfN / 2 + N % 2 + 1)

def step (s : State) (rst : Bit) (i : Input) : State :=
  if rst then
    { s with
      doneReg := false
      state := CtlState.RESET }
  else
    match s.state with
    | CtlState.RESET =>
        { s with
          sqrt := bv 0
          rem := bv 0
          doneReg := false
          count := cv 0
          currentBit := bv 0
          state := if i.start then CtlState.START else CtlState.RESET }
    | CtlState.START =>
        { s with
          currentBit := startBit
          rem := i.in_
          state := CtlState.RUN }
    | CtlState.RUN =>
        let p := prod s
        if s.count = runLimit then
          { s with
            state := CtlState.DONE
            doneReg := true }
        else if s.rem.toNat >= p.toNat then
          { s with
            rem := s.rem - p
            sqrt := shr1 s.sqrt + s.currentBit
            currentBit := shr2 s.currentBit
            count := s.count + cv 1 }
        else
          { s with
            sqrt := shr1 s.sqrt
            currentBit := shr2 s.currentBit
            count := s.count + cv 1 }
    | CtlState.DONE =>
        { s with
          state := CtlState.DONE }

def out (s : State) : Output :=
  { out := s.sqrt
    done := s.doneReg }

@[simp] theorem out_eq (s : State) :
    out s = { out := s.sqrt, done := s.doneReg } := by
  rfl

@[simp] theorem step_reset (s : State) (i : Input) :
    step s true i = { s with doneReg := false, state := CtlState.RESET } := by
  simp [step]

@[simp] theorem step_from_RESET_idle :
    step init false { start := false, in_ := bv 99 } = init := by
  native_decide

@[simp] theorem step_from_RESET_start :
    step init false { start := true, in_ := bv 99 } =
      { rem := bv 0
        sqrt := bv 0
        currentBit := bv 0
        count := cv 0
        state := CtlState.START
        doneReg := false } := by
  native_decide

@[simp] theorem step_from_START :
    step
      { rem := bv 0
        sqrt := bv 0
        currentBit := bv 0
        count := cv 0
        state := CtlState.START
        doneReg := false }
      false
      { start := false, in_ := bv 144 } =
      { rem := bv 144
        sqrt := bv 0
        currentBit := startBit
        count := cv 0
        state := CtlState.RUN
        doneReg := false } := by
  native_decide

@[simp] theorem step_run_to_done :
    step
      { rem := bv 0
        sqrt := bv 12
        currentBit := bv 1
        count := runLimit
        state := CtlState.RUN
        doneReg := false }
      false
      { start := false, in_ := bv 0 } =
      { rem := bv 0
        sqrt := bv 12
        currentBit := bv 1
        count := runLimit
        state := CtlState.DONE
        doneReg := true } := by
  native_decide

@[simp] theorem step_run_subtract :
    step
      { rem := bv 9
        sqrt := bv 4
        currentBit := bv 1
        count := cv 0
        state := CtlState.RUN
        doneReg := false }
      false
      { start := false, in_ := bv 0 } =
      { rem := bv 4
        sqrt := bv 3
        currentBit := bv 0
        count := cv 1
        state := CtlState.RUN
        doneReg := false } := by
  native_decide

@[simp] theorem step_run_shift :
    step
      { rem := bv 3
        sqrt := bv 4
        currentBit := bv 1
        count := cv 0
        state := CtlState.RUN
        doneReg := false }
      false
      { start := false, in_ := bv 0 } =
      { rem := bv 3
        sqrt := bv 2
        currentBit := bv 0
        count := cv 1
        state := CtlState.RUN
        doneReg := false } := by
  native_decide

@[simp] theorem step_done_hold :
    step
      { rem := bv 1
        sqrt := bv 2
        currentBit := bv 4
        count := cv 9
        state := CtlState.DONE
        doneReg := true }
      false
      { start := true, in_ := bv 7 } =
      { rem := bv 1
        sqrt := bv 2
        currentBit := bv 4
        count := cv 9
        state := CtlState.DONE
        doneReg := true } := by
  native_decide

end intSqrt
