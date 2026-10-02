/- Opt-in, non-authoritative coarse audit timings. No payload or credential
bytes are retained or printed. Disabled wrappers are exactly their actions. -/
import Init.System.IO

namespace Minidregg.Kernel.AuditTiming
set_option autoImplicit false

structure Total where
  phase : String
  count : Nat
  nanos : Nat

abbrev Handle := Option (IO.Ref (List Total))

private def add (phase : String) (nanos : Nat) : List Total → List Total
  | [] => [⟨phase, 1, nanos⟩]
  | row :: rest =>
      if row.phase == phase then { row with count := row.count + 1, nanos := row.nanos + nanos } :: rest
      else row :: add phase nanos rest

private def record (sink : IO.Ref (List Total)) (phase : String) (started : Nat) : IO Unit := do
  let stopped ← IO.monoNanosNow
  sink.modify (add phase (stopped - started))

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
    return some (← IO.mkRef [])
  else return none

/-- Timing output is an operator diagnostic, never a new audit failure. -/
def report (timing : Handle) : IO Unit := do
  match timing with
  | none => pure ()
  | some sink =>
      try
        for row in ← sink.get do
          IO.eprintln s!"audit-timing phase={row.phase} count={row.count} nanos={row.nanos}"
      catch _ => pure ()

@[simp] theorem report_disabled : report none = pure () := rfl
end Minidregg.Kernel.AuditTiming
