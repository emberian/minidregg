/-
Physical candidate for an event26 lifetime agent dispatch. This is a
point-in-time projection, not a delivery permit. The original session-origin
generation remains in the base dispatch; the separately projected parent is
the current execution fence and may have a later generation.
-/
module

public import Kernel.ApplicationAgentLifetimeDispatchCore
public import Kernel.ApplicationDispatchAgentProjection

-- Bodies this file reduces or derives through, not exposed by their modules (module system).
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.ToString.Extra
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Control.Except
import all Init.Data.List.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.Format.Basic
import all Init.Data.List.Scan.Basic

@[expose] public section

namespace Minidregg.Kernel.ApplicationAgentLifetimeDispatchProjection

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.NativeHost

set_option autoImplicit false

/-- The grant identity and certified issue index are inside `context`. The
original ticket issue retains its full receipt and source descriptor, and the
grant retains its certified initialized root alongside the current physical
root. The parent and purse roots are current-image process fences. -/
structure Paid where
  candidate : ApplicationDispatchAgentProjection.Candidate
  context : ApplicationAgentLifetimeDispatchReserveContext.Context
  originalIssueIndex : Nat
  originalIssueReceipt : NativeHostCodec.Receipt
  originalIssueDescriptor : List UInt8
  grantIssueReceipt : NativeHostCodec.Receipt
  grantInitializedRoot : Digest
  grantPhysicalRoot : Digest
  reserveIndex : Nat
  reserveReceipt : NativeHostCodec.Receipt
  reserveNonce : Nat
  pursePhysicalRoot : Digest
  deriving DecidableEq

def paidStream : StreamCodec Paid :=
  StreamCodec.xmap
    (StreamCodec.product ApplicationDispatchAgentProjection.candidateStream
      (StreamCodec.product ApplicationAgentLifetimeDispatchReserveContext.contextStream
        (StreamCodec.product StreamCodec.nat
          (StreamCodec.product NativeHostCodec.receiptStream
            (StreamCodec.product bytesStream
              (StreamCodec.product NativeHostCodec.receiptStream
                (StreamCodec.product digestStream
                  (StreamCodec.product digestStream
                    (StreamCodec.product StreamCodec.nat
                      (StreamCodec.product NativeHostCodec.receiptStream
                        (StreamCodec.product StreamCodec.nat digestStream)))))))))))
    (fun paid => (paid.candidate, paid.context, paid.originalIssueIndex,
      paid.originalIssueReceipt, paid.originalIssueDescriptor,
      paid.grantIssueReceipt, paid.grantInitializedRoot, paid.grantPhysicalRoot,
      paid.reserveIndex, paid.reserveReceipt, paid.reserveNonce,
      paid.pursePhysicalRoot))
    (fun (candidate, context, originalIssueIndex, originalIssueReceipt,
          originalIssueDescriptor, grantIssueReceipt, grantInitializedRoot,
          grantPhysicalRoot, reserveIndex, reserveReceipt, reserveNonce,
          pursePhysicalRoot) =>
      ⟨candidate, context, originalIssueIndex, originalIssueReceipt,
        originalIssueDescriptor, grantIssueReceipt, grantInitializedRoot,
        grantPhysicalRoot, reserveIndex, reserveReceipt, reserveNonce,
        pursePhysicalRoot⟩)
    (by intro paid; cases paid; rfl)

def paidCodec : LawfulCodec Paid :=
  NativeHostCodec.framed
    "DREGG/APPLICATION/AGENT-LIFETIME-DISPATCH-PAID-CANDIDATE/v3".toUTF8.toList
    paidStream

def Paid.canonicalBytes (paid : Paid) : List UInt8 := paidCodec.encode paid

theorem decode_encode (paid : Paid) :
    paidCodec.decode paid.canonicalBytes = some paid :=
  paidCodec.decode_encode paid

theorem canonicalBytes_injective : Function.Injective Paid.canonicalBytes := by
  intro left right same
  have decoded := congrArg paidCodec.decode same
  exact Option.some.inj (by simpa only [decode_encode] using decoded)

/-- The source of every field is the Replay-minted event26 admission and its
checked current image. Historical session origin is retained inside
`dispatch`; current parent generation is projected separately. -/
def ofChecked {config : Config} {ground : ServedBasis.Ground config.deployment}
    {ingress : ApplicationAgentLifetimeDispatchIngress.Ingress} (issue : ApplicationDispatchHistoricalCore.IssuedEvidence config)
    {grant : ApplicationAgentLifetimeGrant.Grant} {ticketIndex grantIndex : Nat}
    {ticketReceipt : NativeHostCodec.Receipt} {grantRoot : Digest}
    {reserved : ApplicationAgentLifetimeDispatchReserveCore.ReservedEvidence config}
    (checked : ApplicationAgentLifetimeDispatchCore.Checked config ground ingress issue.spec issue.descriptor grant
      ticketIndex ticketReceipt issue.ingressBytes grantIndex grantRoot reserved)
    (grantReceipt : NativeHostCodec.Receipt) (reserveIndex : Nat) (reserveReceipt : NativeHostCodec.Receipt) :
    Option Paid := do
  let dispatch := ingress.dispatch.dispatch.dispatch
  let current := checked.current
  let claimed ← ingress.dispatch.parent
  let task := ingress.reserveContext.base.parentTask
  if claimed.task != task ||
      claimed.state.generation != ingress.reserveContext.base.parentGeneration ||
      !(claimed.state.status == 3 || claimed.state.status == 4) then none else
  let cell ← match ground.directory.slots task with
    | .present cell => some cell
    | _ => none
  let ⟨.declaredObject, payload⟩ := cell
    | none
  let page := payload.logical
  let state ← AgentGrain.readState task page
  if state != claimed.state || payload.root != claimed.root ||
      state.remaining < 0 || state.reserved < 0 then none else
  let pending := ApplicationAgentLifetimeDispatchCore.candidateIntent checked
  let base : ApplicationDispatchProjection.Candidate :=
    { dispatch := dispatch
      effectiveBits := current.bits
      sessionFingerprint := ApplicationDispatchAdmission.sessionFingerprintOfKey
        (ApplicationDispatchAdmission.sessionFingerprintKeyFor
          ground.authority.cell.root current.selection
          ingress.dispatch current.bits issue.spec.ticket.resource)
      ticketResource := issue.spec.ticket.resource
      ticketRoot := ingress.dispatch.ticketRoot
      enrollmentResource := ingress.dispatch.dispatch.enrollmentResource
      enrollmentRoot := ingress.dispatch.dispatch.enrollmentRoot
      authorityRoot := ground.authority.cell.root
      appRoot := ingress.dispatch.dispatch.appRoot
      sessionRoot := current.selection.sessionRoot
      issueTransaction := issue.transactionId
      issueEvent := issue.eventId
      dispatchTransaction := pending.transactionId
      dispatchEvent := pending.event.eventId
      currentWorldRoot := ground.worldRoot
      physicalRequestDigest := ApplicationDispatchCodec.requestDigest dispatch.request }
  let parent : ApplicationDispatchAgentProjection.Parent :=
    ⟨task, state.generation, state.status, state.remaining, state.reserved,
      payload.root, ResourceBirthCodec.physicalRoot (.live cell)⟩
  some
    { candidate := ⟨base, parent⟩
      context := ingress.reserveContext
      originalIssueIndex := ticketIndex
      originalIssueReceipt := ticketReceipt
      originalIssueDescriptor := (ResourceBirthCodec.descriptorCodec
        CanonicalCellRegistry.registry).encode issue.descriptor
      grantIssueReceipt := grantReceipt
      grantInitializedRoot := grantRoot
      grantPhysicalRoot := ResourceBirthCodec.physicalRoot
        (.live current.grantRead.selected.observed.before)
      reserveIndex := reserveIndex
      reserveReceipt := reserveReceipt
      reserveNonce := ApplicationAgentLifetimeDispatchReserveContext.reserveNonce
        ingress.reserveContext
      pursePhysicalRoot := ResourceBirthCodec.physicalRoot
        (.live checked.payer.cell) }

def ofLifetimeDispatchAt {config : Config} {opened : Opened config}
    {ingress : ApplicationAgentLifetimeDispatchIngress.Ingress}
    (admitted : NativeHostReplay.LifetimeDispatchAt config opened ingress) :
    Option Paid :=
  ofChecked admitted.issue.evidence admitted.checked admitted.grant.receipt admitted.reserve.index admitted.reserve.raw.receipt

end Minidregg.Kernel.ApplicationAgentLifetimeDispatchProjection
