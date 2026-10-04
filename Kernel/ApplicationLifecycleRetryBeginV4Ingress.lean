/- Versioned retry BEGIN. Its source-derived signed operation nonce commits to
the full exact recovery selector and original launch selection. Legacy v3
shape/admission and permanent first-attempt refusal are unchanged. -/
import Kernel.ApplicationFailedCreateRetryEvidence

namespace Minidregg.Kernel.ApplicationLifecycleRetryBeginV4Ingress

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Theory.IndexedProgram
open Minidregg.Compiler.Tower256ConcreteBackend

set_option autoImplicit false

structure Ingress where
  begin : ApplicationLifecycleBeginV3Ingress.Ingress
  retry : ApplicationFailedCreateRetryEvidence.Selector
  deriving DecidableEq

def ingressStream : StreamCodec Ingress :=
  StreamCodec.xmap
    (StreamCodec.product ApplicationLifecycleBeginV3Ingress.ingressStream
      ApplicationFailedCreateRetryEvidence.selectorStream)
    (fun ingress => (ingress.begin, ingress.retry))
    (fun (begin, retry) => ⟨begin, retry⟩)
    (by intro ingress; cases ingress; rfl)

def codec : LawfulCodec Ingress := NativeHostCodec.framed
  "DREGG/APPLICATION/RETRY-CREATE-BEGIN-INGRESS/v4".toUTF8.toList ingressStream

def Ingress.canonicalBytes (ingress : Ingress) : List UInt8 := codec.encode ingress

def authorizationCodec : LawfulCodec (List UInt8 × List UInt8) :=
  NativeHostCodec.framed
    "DREGG/APPLICATION/RETRY-CREATE-BEGIN-AUTHORIZATION/v4".toUTF8.toList
    (StreamCodec.product bytesStream bytesStream)

def authorizationBytes (ingress : Ingress) : List UInt8 :=
  authorizationCodec.encode
    (ApplicationLifecycleBeginV3Ingress.authorizationBytes ingress.begin,
      ingress.retry.canonicalBytes)

def Ingress.authorizationOperationId (ingress : Ingress) : Nat :=
  (Sp800185Cshake256.hash
    "DREGG/APPLICATION/RETRY-CREATE-BEGIN-AUTHORIZATION-ID/v4".toUTF8.toList
    (authorizationBytes ingress)).digest.value

def Ingress.withAuthorizationId (ingress : Ingress) : Ingress :=
  { ingress with begin := { ingress.begin with base :=
      { ingress.begin.base with source :=
          { ingress.begin.base.source with operationId := ingress.authorizationOperationId } } } }

/-- Reuse the complete v3 descriptor/action checks after normalizing only its
old nonce. The actual signed command retains the v4 nonce checked below. -/
def Ingress.shape (ingress : Ingress) : Bool :=
  ingress.begin.base.source.operationId == ingress.authorizationOperationId &&
    ingress.begin.withAuthorizationId.shape &&
    ApplicationFailedCreateRetryEvidence.bindingMatches ingress.retry ingress.begin

theorem decoded_canonical {bytes : List UInt8} {ingress : Ingress}
    (decoded : codec.decode bytes = some ingress) : ingress.canonicalBytes = bytes :=
  NativeHostCodec.framed_canonical
    "DREGG/APPLICATION/RETRY-CREATE-BEGIN-INGRESS/v4".toUTF8.toList ingressStream decoded

theorem authorizationBytes_retry_eq (left right : Ingress)
    (same : authorizationBytes left = authorizationBytes right) : left.retry = right.retry := by
  have selectors : left.retry.canonicalBytes = right.retry.canonicalBytes :=
    congrArg Prod.snd ((lawful_encode_injective authorizationCodec) same)
  exact (lawful_encode_injective ApplicationFailedCreateRetryEvidence.selectorCodec) selectors

theorem authorizationBytes_ignores_operationId (ingress : Ingress) :
    authorizationBytes ingress.withAuthorizationId = authorizationBytes ingress := by
  simp [authorizationBytes, Ingress.withAuthorizationId,
    ApplicationLifecycleBeginV3Ingress.authorizationBytes]

theorem withAuthorizationId_authorized (ingress : Ingress) :
    ingress.withAuthorizationId.begin.base.source.operationId =
      ingress.withAuthorizationId.authorizationOperationId := by
  change ingress.authorizationOperationId = ingress.withAuthorizationId.authorizationOperationId
  simp only [Ingress.authorizationOperationId, authorizationBytes_ignores_operationId]

/-- Payload projections preserve the full wrapper; they are not v3 admission. -/
def Ingress.base (ingress : Ingress) := ingress.begin.base
def Ingress.start (ingress : Ingress) := ingress.begin.start
def Ingress.volume (ingress : Ingress) := ingress.begin.volume
def Ingress.descriptor (ingress : Ingress) := ingress.begin.descriptor
def prospectiveManifest (ingress : Ingress) :=
  ApplicationLifecycleBeginV3Ingress.prospectiveManifest ingress.begin

end Minidregg.Kernel.ApplicationLifecycleRetryBeginV4Ingress
