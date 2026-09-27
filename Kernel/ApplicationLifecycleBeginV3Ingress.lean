/-
Additive lifecycle BEGIN for a signed-SPK launch descriptor and a grain's
persistent volume. The v1/v2 BEGIN frames and their replay remain unchanged.
Only START carries an exact create/continue binding; INSTALL and UPGRADE
install the reusable package identity, while STOP has no launch command.
The receiving path must still check current authority, installed package and
the verified launch-history choice before admitting this pending operation.
-/
import Kernel.ApplicationLifecycleBeginIngress
import Kernel.ApplicationSpkLaunchDescriptor
import Kernel.ApplicationLifecycleLaunchBinding

namespace Minidregg.Kernel.ApplicationLifecycleBeginV3Ingress

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.DurableDataIntent

set_option autoImplicit false

structure Ingress where
  base : ApplicationLifecycleBeginIngress.Ingress
  /-- Caller-selected correlation/idempotency identity. The signed base
  operation ID is derived below; it is not a free caller integer in v3. -/
  clientOperationId : Nat
  descriptor : ApplicationSpkLaunchDescriptor.Descriptor
  volume : Digest
  start : Option ApplicationLifecycleLaunchBinding.Binding
  deriving DecidableEq, Repr

def ingressStream : StreamCodec Ingress :=
  StreamCodec.xmap
    (StreamCodec.product ApplicationLifecycleBeginIngress.ingressStream
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product ApplicationSpkLaunchDescriptor.descriptorStream
          (StreamCodec.product digestStream
            (StreamCodec.option ApplicationLifecycleLaunchBinding.bindingStream)))))
    (fun ingress => (ingress.base, ingress.clientOperationId,
      ingress.descriptor, ingress.volume, ingress.start))
    (fun (base, clientOperationId, descriptor, volume, start) =>
      ⟨base, clientOperationId, descriptor, volume, start⟩)
    (by intro ingress; cases ingress; rfl)

def frame : List UInt8 :=
  "DREGG/APPLICATION/LIFECYCLE-BEGIN-INGRESS/v3".toUTF8.toList

def codec : LawfulCodec Ingress := NativeHostCodec.framed frame ingressStream

def Ingress.canonicalBytes (ingress : Ingress) : List UInt8 := codec.encode ingress

/-- The old BEGIN mutation command signs the `Source` nonce. For v3 that
source's operation ID is a source-derived commitment to the *whole* launch
selection. Without this check, changing a create action while retaining the
same `base` would retain the same authorized mutation command. The versioned
preimage zeros the operation ID to avoid a circular definition, and includes
the exact descriptor, volume, choice, command digest and prior-create selector.
The native signature verifier still checks the resulting old signed command;
collision resistance of this digest is the same deployment premise as the
existing source-derived DRC nonce, not a Lean injectivity claim. -/
abbrev AuthorizationTuple := Digest × Digest × ApplicationLifecycleBegin.Source ×
  Nat × ApplicationSpkLaunchDescriptor.Descriptor × Digest ×
  Option ApplicationLifecycleLaunchBinding.Binding

def authorizationStream : StreamCodec AuthorizationTuple :=
  StreamCodec.product digestStream
    (StreamCodec.product digestStream
      (StreamCodec.product ApplicationLifecycleBegin.sourceStream
        (StreamCodec.product StreamCodec.nat
          (StreamCodec.product ApplicationSpkLaunchDescriptor.descriptorStream
            (StreamCodec.product digestStream
              (StreamCodec.option ApplicationLifecycleLaunchBinding.bindingStream))))))

def authorizationCodec : LawfulCodec AuthorizationTuple :=
  NativeHostCodec.framed
    "DREGG/APPLICATION/LIFECYCLE-BEGIN-AUTHORIZATION/v3".toUTF8.toList
    authorizationStream

def authorizationBytes (ingress : Ingress) : List UInt8 :=
  authorizationCodec.encode
    (ingress.base.domain, ingress.base.semantics,
      { ingress.base.source with operationId := 0 }, ingress.clientOperationId,
      ingress.descriptor, ingress.volume, ingress.start)

/-- Changing the exact selected action or prior-create selector changes the
versioned authorization preimage. This is a codec fact; the later digest's
collision resistance remains a deployment premise. -/
theorem authorizationBytes_start_eq (left right : Ingress)
    (same : authorizationBytes left = authorizationBytes right) :
    left.start = right.start := by
  have tupleEq := (lawful_encode_injective authorizationCodec) same
  exact congrArg (fun tuple : AuthorizationTuple => tuple.2.2.2.2.2.2) tupleEq

def Ingress.authorizationOperationId (ingress : Ingress) : Nat :=
  (Sp800185Cshake256.hash
    "DREGG/APPLICATION/LIFECYCLE-BEGIN-AUTHORIZATION-ID/v3".toUTF8.toList
    (authorizationBytes ingress)).digest.value

def Ingress.withAuthorizationId (ingress : Ingress) : Ingress :=
  { ingress with base :=
      { ingress.base with source :=
          { ingress.base.source with operationId := ingress.authorizationOperationId } } }

theorem authorizationBytes_ignores_operationId (ingress : Ingress) :
    authorizationBytes ingress.withAuthorizationId = authorizationBytes ingress := by
  simp [authorizationBytes, Ingress.withAuthorizationId]

theorem withAuthorizationId_authorized (ingress : Ingress) :
    ingress.withAuthorizationId.base.source.operationId =
      ingress.withAuthorizationId.authorizationOperationId := by
  change ingress.authorizationOperationId =
    ingress.withAuthorizationId.authorizationOperationId
  simp only [Ingress.authorizationOperationId,
    authorizationBytes_ignores_operationId]

theorem decode_encode (ingress : Ingress) :
    codec.decode ingress.canonicalBytes = some ingress := codec.decode_encode ingress

theorem decoded_canonical {bytes : List UInt8} {ingress : Ingress}
    (decoded : codec.decode bytes = some ingress) :
    ingress.canonicalBytes = bytes :=
  NativeHostCodec.framed_canonical frame ingressStream decoded

def event (ingress : Ingress) : StableEvent where
  codecVersion := 23
  domain := ingress.base.domain
  eventId := (Sp800185Cshake256.hash
    "DREGG/APPLICATION/LIFECYCLE-BEGIN-EVENT/v3".toUTF8.toList
    ingress.canonicalBytes).digest
  canonicalBytes := ingress.canonicalBytes

def prospectiveVersion (source : ApplicationLifecycleBegin.Source) : Int :=
  match source.kind with
  | .install | .upgrade => source.before.packageVersion + 1
  | .start | .stop => source.before.packageVersion

def prospectiveManifest (ingress : Ingress) : ApplicationDispatchManifest.Manifest :=
  { app := ingress.base.source.app
    packageVersion := prospectiveVersion ingress.base.source
    packageRoot := ingress.descriptor.root
    interfaces := ingress.descriptor.package.interfaces }

/-- This exact shape is necessary but not sufficient. In particular,
`priorCreate` is a selector, not proof that its receipt came from a successful
physical create. Verified history supplies that certificate separately. -/
def Ingress.shape (ingress : Ingress) : Bool :=
  let source := ingress.base.source
  source.operationId == ingress.authorizationOperationId &&
    source.valid && ingress.descriptor.matchesManifest (prospectiveManifest ingress) &&
    source.packageDigest == ingress.descriptor.root &&
    source.imageIdentity == ingress.descriptor.package.imageIdentity &&
    ingress.volume == ApplicationLifecycleLaunchBinding.volumeId ingress.base.domain source.app &&
    match source.kind, ingress.start with
    | .start, some binding =>
        binding.app == source.app && binding.volume == ingress.volume &&
          binding.valid ingress.base.domain ingress.descriptor
    | .install, none | .stop, none | .upgrade, none => true
    | _, _ => false

theorem shape_authorizationId (ingress : Ingress)
    (shape : ingress.shape = true) :
    ingress.base.source.operationId = ingress.authorizationOperationId := by
  simp only [Ingress.shape, Bool.and_eq_true, beq_iff_eq] at shape
  aesop

/-- The legacy signed command alone cannot distinguish two v3 choices with
the same base. `shape_authorizationId` is the additional source check that
rejects such substitution unless the versioned authorization digests collide. -/
theorem same_base_same_legacy_command (left right : Ingress)
    (same : left.base = right.base) :
    ApplicationLifecycleBegin.command left.base.domain left.base.semantics
      left.base.source =
    ApplicationLifecycleBegin.command right.base.domain right.base.semantics
      right.base.source := by
  rw [same]

theorem event_retains_full_ingress (ingress : Ingress) :
    (event ingress).canonicalBytes = ingress.canonicalBytes := rfl

theorem nonstart_has_no_binding (ingress : Ingress)
    (shape : ingress.shape = true)
    (kind : ingress.base.source.kind ≠ .start) : ingress.start = none := by
  cases h : ingress.start with
  | none => rfl
  | some binding =>
      cases k : ingress.base.source.kind <;>
        simp [Ingress.shape, h, k] at shape
      exact False.elim (kind k)

end Minidregg.Kernel.ApplicationLifecycleBeginV3Ingress
