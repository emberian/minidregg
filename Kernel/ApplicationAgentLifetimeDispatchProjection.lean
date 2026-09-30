/-
Physical candidate for an event26 lifetime agent dispatch. This is a
point-in-time projection, not a delivery permit. The original session-origin
generation remains in the base dispatch; the separately projected parent is
the current execution fence and may have a later generation.
-/
import Kernel.ApplicationAgentLifetimeDispatchCore
import Kernel.ApplicationDispatchAgentProjection

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
def ofLifetimeDispatchAt {config : Config} {opened : Opened config}
    {ingress : ApplicationAgentLifetimeDispatchIngress.Ingress}
    (admitted : NativeHostReplay.LifetimeDispatchAt config opened ingress) :
    Option Paid := do
  let dispatch := ingress.dispatch.dispatch.dispatch
  let current := admitted.checked.current
  let claimed ← ingress.dispatch.parent
  let task := ingress.reserveContext.base.parentTask
  if claimed.task != task ||
      claimed.state.generation != ingress.reserveContext.base.parentGeneration ||
      !(claimed.state.status == 3 || claimed.state.status == 4) then none else
  let cell ← match opened.directory.directory.slots task with
    | .present cell => some cell
    | _ => none
  let ⟨.declaredObject, payload⟩ := cell
    | none
  let page := payload.logical
  let state ← AgentGrain.readState task page
  if state != claimed.state || payload.root != claimed.root ||
      state.remaining < 0 || state.reserved < 0 then none else
  let pending := admitted.intent
  let base : ApplicationDispatchProjection.Candidate :=
    { dispatch := dispatch
      effectiveBits := current.bits
      sessionFingerprint := ApplicationDispatchAdmission.sessionFingerprintOfKey
        (ApplicationDispatchAdmission.sessionFingerprintKeyFor current.selection
          ingress.dispatch current.bits admitted.issue.evidence.spec.ticket.resource)
      ticketResource := admitted.issue.evidence.spec.ticket.resource
      ticketRoot := ingress.dispatch.ticketRoot
      enrollmentResource := ingress.dispatch.dispatch.enrollmentResource
      enrollmentRoot := ingress.dispatch.dispatch.enrollmentRoot
      authorityRoot := current.selection.authorityRoot
      appRoot := ingress.dispatch.dispatch.appRoot
      sessionRoot := current.selection.sessionRoot
      issueTransaction := admitted.issue.evidence.transactionId
      issueEvent := admitted.issue.evidence.eventId
      dispatchTransaction := pending.transactionId
      dispatchEvent := pending.event.eventId
      currentImageBoundary := imageBoundary config opened.durable.image
      physicalRequestDigest := ApplicationDispatchCodec.requestDigest dispatch.request }
  let parent : ApplicationDispatchAgentProjection.Parent :=
    ⟨task, state.generation, state.status, state.remaining, state.reserved,
      payload.root, ResourceBirthCodec.physicalRoot (.live cell)⟩
  some
    { candidate := ⟨base, parent⟩
      context := ingress.reserveContext
      originalIssueIndex := admitted.issue.index
      originalIssueReceipt := admitted.issue.receipt
      originalIssueDescriptor := (ResourceBirthCodec.descriptorCodec
        CanonicalCellRegistry.registry).encode admitted.issue.evidence.descriptor
      grantIssueReceipt := admitted.grant.receipt
      grantInitializedRoot := admitted.grant.finalRoot
      grantPhysicalRoot := ResourceBirthCodec.physicalRoot
        (.live current.grantRead.selected.observed.before)
      reserveIndex := admitted.reserve.index
      reserveReceipt := admitted.reserve.raw.receipt
      reserveNonce := ApplicationAgentLifetimeDispatchReserveContext.reserveNonce
        ingress.reserveContext
      pursePhysicalRoot := ResourceBirthCodec.physicalRoot
        (.live admitted.checked.payer.cell) }

end Minidregg.Kernel.ApplicationAgentLifetimeDispatchProjection
