/- Low current pending-phase permit for the explicit typed application route.
The source-selected runtime profile chooses the pin; the snapshot is the actual
prepared native snapshot. This module neither authorizes signatures nor proves
history. Protected-coordinate replay supplies provenance, and the typed native
controller must retain this exact physical guard in its final admitted intent.
-/
import Kernel.BendActivity
import Compiler.ContentControlFrame
import Compiler.NativeInvocationStatement
import Compiler.BendActivityDispatchContext

namespace Minidregg.Kernel.BendActivityRoutePermit
open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler
open Minidregg.Kernel.DurableDataIntent
set_option autoImplicit false

structure Permit {rootBytes : List UInt8 → Digest}
    (snapshot : DataSnapshot rootBytes) (pin : ContentControlFrame.Pin)
    (statement : NativeInvocationStatement.Statement) (ingressBytes : List UInt8) where
  private mk ::
  record : BendActivity.Record
  pending : BendActivity.Pending
  current : ContentControlFrame.readPayload pin (snapshot.canonicalBytes pin.cell) =
    some (BendActivity.encode record)
  pendingExact : record.pending = some pending
  applicationExact : pending.applicationSignedBytes = ingressBytes
  dispatchRoute : statement.route = .activityDispatch
  context : BendActivityDispatchContext.Context
  contextExact : BendActivityDispatchContext.decode statement.contextBytes = some context
  pinExact : ContentControlFrame.pinStream.encode context.pin = ContentControlFrame.pinStream.encode pin
  generationExact : context.generation = record.checkpoint.generation
  ordinalExact : context.pendingOrdinal = record.ordinal

def admit {rootBytes : List UInt8 → Digest} (snapshot : DataSnapshot rootBytes)
    (pin : ContentControlFrame.Pin) (statement : NativeInvocationStatement.Statement) (ingressBytes : List UInt8) :
    Option (Permit snapshot pin statement ingressBytes) := do
  let bytes ← ContentControlFrame.readPayload pin (snapshot.canonicalBytes pin.cell)
  let record ← BendActivity.decode bytes
  if current : ContentControlFrame.readPayload pin (snapshot.canonicalBytes pin.cell) =
      some (BendActivity.encode record) then
    match pendingExact : record.pending with
    | none => none
    | some pending =>
      if applicationExact : pending.applicationSignedBytes = ingressBytes then
        if dispatchRoute : statement.route = .activityDispatch then
          match contextExact : BendActivityDispatchContext.decode statement.contextBytes with
          | none => none
          | some context =>
            if pinExact : ContentControlFrame.pinStream.encode context.pin = ContentControlFrame.pinStream.encode pin then
              if generationExact : context.generation = record.checkpoint.generation then
                if ordinalExact : context.pendingOrdinal = record.ordinal then
                  some ⟨record,pending,current,pendingExact,applicationExact,dispatchRoute,
                    context,contextExact,pinExact,generationExact,ordinalExact⟩
                else none
              else none
            else none
        else none
      else none
  else none

def Permit.guard {rootBytes : List UInt8 → Digest} {snapshot : DataSnapshot rootBytes}
    {pin : ContentControlFrame.Pin} {statement : NativeInvocationStatement.Statement} {ingressBytes : List UInt8}
    (_permit : Permit snapshot pin statement ingressBytes) : ReadGuard :=
  ⟨pin.cell,snapshot.model.roots pin.cell⟩

theorem guard_current {rootBytes : List UInt8 → Digest} {snapshot : DataSnapshot rootBytes}
    {pin : ContentControlFrame.Pin} {statement : NativeInvocationStatement.Statement} {ingressBytes : List UInt8}
    (permit : Permit snapshot pin statement ingressBytes) :
    permit.guard.expectedRoot = snapshot.model.roots pin.cell := rfl

#assert_axioms admit
#assert_axioms guard_current
end Minidregg.Kernel.BendActivityRoutePermit
