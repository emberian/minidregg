/- Opt-in, non-authoritative coarse audit timings. No payload or credential
bytes are retained or printed. Disabled wrappers are exactly their actions. -/
import Init.System.IO

namespace Minidregg.Kernel.AuditTiming
set_option autoImplicit false

structure Total where
  phase : String
  count : Nat
  nanos : Nat

structure Progress where
  index : Nat
  family : String

structure State where
  totals : List Total := []
  current : Option Progress := none

abbrev Handle := Option (IO.Ref State)

private def add (phase : String) (nanos : Nat) : List Total → List Total
  | [] => [⟨phase, 1, nanos⟩]
  | row :: rest =>
      if row.phase == phase then { row with count := row.count + 1, nanos := row.nanos + nanos } :: rest
      else row :: add phase nanos rest

private def record (sink : IO.Ref State) (phase : String) (started : Nat) : IO Unit := do
  let stopped ← IO.monoNanosNow
  sink.modify fun state => { state with totals := add phase (stopped - started) state.totals }

/-- The phase thunk is evaluated only when enabled; disabled operation does
not even classify an ingress. No changes to the action's result or errors. -/
def measure {α : Type} (timing : Handle) (phase : Unit → String) (action : IO α) : IO α :=
  match timing with
  | none => action
  | some sink => do
      let started ← IO.monoNanosNow
      try action finally record sink (phase ()) started

/-- Delay pure work until after the timer starts. Carry its exact value proof
so admission/advance/validation retain their original semantic witnesses. -/
def value {α : Type} (timing : Handle) (phase : Unit → String) (action : Unit → α) :
    IO {result : α // result = action ()} :=
  match timing with
  | none => pure ⟨action (), rfl⟩
  | some sink => do
      let started ← IO.monoNanosNow
      let result := action ()
      record sink (phase ()) started
      pure ⟨result, rfl⟩

@[simp] theorem measure_disabled {α : Type} (phase : Unit → String) (action : IO α) :
    measure none phase action = action := rfl

@[simp] theorem value_disabled {α : Type} (phase : Unit → String) (action : Unit → α) :
    value none phase action = pure ⟨action (), rfl⟩ := rfl

def fromEnvironment : IO Handle := do
  if (← IO.getEnv "MINI_AUDIT_TIMING") == some "1" then
    return some (← IO.mkRef ({} : State))
  else return none

/-- Timing output is an operator diagnostic, never a new audit failure.
Each report is cumulative. The current index is zero-based; a progress report
is emitted before admitting that record, after all prior records were checked. -/
def report (timing : Handle) (status : String := "final") : IO Unit := do
  match timing with
  | none => pure ()
  | some sink =>
      try
        let state ← sink.get
        match state.current with
        | none => IO.eprintln s!"audit-timing status={status} record=none"
        | some current =>
            IO.eprintln s!"audit-timing status={status} record={current.index} family={current.family}"
        for row in state.totals do
          IO.eprintln s!"audit-timing phase={row.phase} count={row.count} nanos={row.nanos}"
      catch _ => pure ()

/-- Retain only the current fixed family and position. Print at record zero
and every sixteen records so termination cannot erase all phase evidence.
The family thunk and interval check are entirely absent when disabled. -/
def beginRecord (timing : Handle) (index : Nat) (family : Unit → String) : IO Unit :=
  match timing with
  | none => pure ()
  | some sink => do
      sink.modify fun state => { state with current := some ⟨index, family ()⟩ }
      if index % 16 == 0 then report timing "progress"

@[simp] theorem report_disabled (status : String) : report none status = pure () := rfl

@[simp] theorem beginRecord_disabled (index : Nat) (family : Unit → String) :
    beginRecord none index family = pure () := rfl
end Minidregg.Kernel.AuditTiming
