/-
The exact app-facing request and current authority projection prepared by
native dispatch admission. This is deliberately a candidate codec, not a
physical delivery permit. Only the special receiver's exact post-CAS branch
may wrap these bytes in a committed delivery envelope.
-/
import Kernel.NativeHostReplay

namespace Minidregg.Kernel.ApplicationDispatchProjection

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.IndexedProgram
open Minidregg.Kernel.NativeHost
open Minidregg.Kernel.ApplicationDispatchCodec

set_option autoImplicit false

/-- Checked app/session identity and rights for one app-side WebSession. The
fingerprint omits per-request workflow state, while the following roots and
tip retain exact current-image authority for this request. -/
structure Candidate where
  dispatch : Dispatch
  effectiveBits : List Bool
  sessionFingerprint : Digest
  ticketResource : Nat
  ticketRoot : Digest
  enrollmentResource : Nat
  enrollmentRoot : Digest
  authorityRoot : Digest
  appRoot : Digest
  sessionRoot : Digest
  issueTransaction : Digest
  issueEvent : Digest
  dispatchTransaction : Digest
  dispatchEvent : Digest
  currentImageBoundary : Digest
  physicalRequestDigest : Digest
  deriving DecidableEq

/-- A transport digest over the exact checked method, path, query, ordered
ordinary headers (including cookies), and full body. The complete request is
also retained in `dispatch`; no digest substitutes for its bytes. -/
def requestDigest (request : Request) : Digest :=
  (Sp800185Cshake256.hash
    "DREGG/APPLICATION/PHYSICAL-WEB-REQUEST/v1".toUTF8.toList
    (requestStream.encode request)).digest

/-- The receiver projects from the same typed replay admission whose intent
it submits to CAS. The prior issue was retained by the verifier's actual
chronological walk, so these bytes cannot be supplied by a caller. -/
def ofDispatchAt {config : Config} {opened : Opened config}
    {ingress : ApplicationDispatchAdmissionIngress.Ingress}
    (admitted : NativeHostReplay.DispatchAt config opened ingress) : Candidate :=
  let dispatch := ingress.dispatch.dispatch
  let checked := admitted.checked.checked
  let pending := admitted.intent
  { dispatch := dispatch
    effectiveBits := checked.bits
    sessionFingerprint := checked.sessionFingerprint
    ticketResource := admitted.prior.evidence.ingress.spec.ticket.resource
    ticketRoot := ingress.ticketRoot
    enrollmentResource := ingress.dispatch.enrollmentResource
    enrollmentRoot := ingress.dispatch.enrollmentRoot
    authorityRoot := checked.selection.authorityRoot
    appRoot := ingress.dispatch.appRoot
    sessionRoot := checked.selection.sessionRoot
    issueTransaction := admitted.prior.evidence.transactionId
    issueEvent := admitted.prior.evidence.eventId
    dispatchTransaction := pending.transactionId
    dispatchEvent := pending.event.eventId
    currentImageBoundary := imageBoundary config opened.durable.image
    physicalRequestDigest := requestDigest dispatch.request }

def candidateStream : StreamCodec Candidate :=
  StreamCodec.xmap
    (StreamCodec.product dispatchStream
      (StreamCodec.product (StreamCodec.list StreamCodec.bool)
        (StreamCodec.product digestStream
          (StreamCodec.product StreamCodec.nat
            (StreamCodec.product digestStream
              (StreamCodec.product StreamCodec.nat
                (StreamCodec.product digestStream
                  (StreamCodec.product digestStream
                    (StreamCodec.product digestStream
                      (StreamCodec.product digestStream
                        (StreamCodec.product digestStream
                          (StreamCodec.product digestStream
                            (StreamCodec.product digestStream
                              (StreamCodec.product digestStream
                                (StreamCodec.product digestStream digestStream)))))))))))))))
    (fun value => (value.dispatch, value.effectiveBits, value.sessionFingerprint,
      value.ticketResource, value.ticketRoot, value.enrollmentResource,
      value.enrollmentRoot, value.authorityRoot, value.appRoot, value.sessionRoot,
      value.issueTransaction, value.issueEvent, value.dispatchTransaction,
      value.dispatchEvent, value.currentImageBoundary, value.physicalRequestDigest))
    (fun (dispatch, effectiveBits, sessionFingerprint, ticketResource, ticketRoot,
          enrollmentResource, enrollmentRoot, authorityRoot, appRoot, sessionRoot,
          issueTransaction, issueEvent, dispatchTransaction, dispatchEvent,
          currentImageBoundary, physicalRequestDigest) =>
      ⟨dispatch, effectiveBits, sessionFingerprint, ticketResource, ticketRoot,
        enrollmentResource, enrollmentRoot, authorityRoot, appRoot, sessionRoot,
        issueTransaction, issueEvent, dispatchTransaction, dispatchEvent,
        currentImageBoundary, physicalRequestDigest⟩)
    (by intro value; cases value; rfl)

def codec : LawfulCodec Candidate :=
  NativeHostCodec.framed
    "DREGG/APPLICATION/DISPATCH-CANDIDATE/v1".toUTF8.toList candidateStream

def Candidate.canonicalBytes (candidate : Candidate) : List UInt8 :=
  codec.encode candidate

theorem decode_encode (candidate : Candidate) :
    codec.decode candidate.canonicalBytes = some candidate :=
  codec.decode_encode candidate

theorem ofDispatchAt_request_exact {config : Config} {opened : Opened config}
    {ingress : ApplicationDispatchAdmissionIngress.Ingress}
    (admitted : NativeHostReplay.DispatchAt config opened ingress) :
    (ofDispatchAt admitted).dispatch.request = ingress.dispatch.dispatch.request := rfl

theorem ofDispatchAt_permission_exact {config : Config} {opened : Opened config}
    {ingress : ApplicationDispatchAdmissionIngress.Ingress}
    (admitted : NativeHostReplay.DispatchAt config opened ingress) :
    (ofDispatchAt admitted).effectiveBits = admitted.checked.checked.bits := rfl

end Minidregg.Kernel.ApplicationDispatchProjection
