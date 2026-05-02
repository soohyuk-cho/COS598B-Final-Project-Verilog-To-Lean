import Std

namespace intSqrt

inductive FsmState where
  | RESET
  | START
  | RUN
  | DONE
deriving Repr, DecidableEq

structure State (n : Nat) where
  rem : BitVec n
  sqrt : BitVec n
  currentBit : BitVec n
  count : BitVec (Nat.log2 n + 1)
  state : FsmState
  doneReg : Bool
deriving Repr, DecidableEq

structure Input (n : Nat) where
  rst : Bool
  start : Bool
  «in» : BitVec n
deriving Repr, DecidableEq

structure Output (n : Nat) where
  out : BitVec n
  done : Bool
deriving Repr, DecidableEq

def init {n : Nat} : State n :=
  { rem := BitVec.ofNat n 0,
    sqrt := BitVec.ofNat n 0,
    currentBit := BitVec.ofNat n 0,
    count := BitVec.ofNat (Nat.log2 n + 1) 0,
    state := FsmState.RESET,
    doneReg := false }

def step {n : Nat} (s : State n) (i : Input n) : State n :=
  if i.rst then
    init
  else
    match s.state with
    | FsmState.RESET =>
      { s with
        sqrt := BitVec.ofNat n 0,
        rem := BitVec.ofNat n 0,
        doneReg := false,
        count := BitVec.ofNat (Nat.log2 n + 1) 0,
        currentBit := BitVec.ofNat n 0,
        state := if i.start then FsmState.START else FsmState.RESET }
    | FsmState.START =>
      -- currentBit logic: {(N & 1), !(N & 1), {(N - 2) {1'b0}}}
      let msb := (n &&& 1) != 0
      let next_msb := (n &&& 1) == 0
      let cb := (if msb then BitVec.ofNat n 1 else BitVec.ofNat n 0) <<< (n - 1) |||
                (if next_msb then BitVec.ofNat n 1 else BitVec.ofNat n 0) <<< (n - 2)
      { s with
        currentBit := cb,
        rem := i.«in»,
        state := FsmState.RUN }
    | FsmState.RUN =>
      -- count == $size(N) / 2 + N % 2 + 1
      -- $size(N) is the number of bits in the count register, but N is the parameter
      -- The loop runs for approx N/2 iterations.
      if s.count.toNat == (n / 2) + (n % 2) + 1 then
        { s with state := FsmState.DONE, doneReg := true }
      else
        let prod := s.sqrt + s.currentBit
        let next_rem := if s.rem >= prod then s.rem - prod else s.rem
        let next_sqrt := if s.rem >= prod then
                           (s.sqrt >>> 1) + s.currentBit
                         else
                           (s.sqrt >>> 1)
        let next_currentBit := s.currentBit >>> 2
        { s with
          rem := next_rem,
          sqrt := next_sqrt,
          currentBit := next_currentBit,
          count := s.count + 1 }
    | FsmState.DONE =>
      { s with state := FsmState.DONE }

def out {n : Nat} (s : State n) : Output n :=
  { out := s.sqrt,
    done := s.doneReg }

@[simp] theorem step_reset {n : Nat} (s : State n) (i : Input n) :
  step s { i with rst := true } = init := by
  simp [step, init]

@[simp] theorem step_done_hold {n : Nat} (s : State n) (i : Input n) :
  s.state = FsmState.DONE ∧ ¬i.rst → (step s i).state = FsmState.DONE := by
  intro h; simp [step, h.1, h.2]

end intSqrt
