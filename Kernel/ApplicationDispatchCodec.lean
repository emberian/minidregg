/-
Canonical application-facing request identity. This codec conveys no authority:
the special receiver must derive the effective identity and permissions from
the installed interface and current participant/session grants, then admit the
exact signed ingress against the loaded Mini image. In particular, a browser
request is not an AgentGrain child merely because a transport uses an agent.
-/
import Kernel.ResourceTransaction

namespace Minidregg.Kernel.ApplicationDispatchCodec

open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.DeclaredEffectPageMaterializer
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.IndexedProgram

set_option autoImplicit false

inductive InterfaceKind where
  | web
  | api
  deriving DecidableEq, Repr

def interfaceKindStream : StreamCodec InterfaceKind :=
  StreamCodec.xmap StreamCodec.bool
    (fun kind => kind == .api)
    (fun encoded => if encoded then .api else .web)
    (by intro kind; cases kind <;> rfl)

/-- `agent` carries the parent task generation; the client cannot omit it
while still claiming an agent-origin request. A human session has no parent
task and is not fenced by that task's cgroup or hard EOF. -/
inductive Origin where
  | human
  | agent (task : Nat) (generation : Int)
  deriving DecidableEq, Repr

def Origin.toWire : Origin → Option (Nat × Int)
  | .human => none
  | .agent task generation => some (task, generation)

def Origin.ofWire : Option (Nat × Int) → Origin
  | none => .human
  | some (task, generation) => .agent task generation

def originStream : StreamCodec Origin :=
  StreamCodec.xmap
    (StreamCodec.option (StreamCodec.product StreamCodec.nat intStream))
    Origin.toWire Origin.ofWire
    (by intro origin; cases origin <;> rfl)

/-- An exact installed interface, not a URL prefix or a caller's assertion
that its HTTP method is observational. Serving phase is checked separately
against the current ApplicationGrain page. -/
structure App where
  resource : Nat
  packageManifest : Nat
  generation : Int
  packageVersion : Int
  snapshotVersion : Int
  packageRoot : Digest
  manifestRoot : Digest
  interfaceId : Nat
  interfaceVersion : Nat
  interfaceRoot : Digest
  capability : CapabilityId
  deriving DecidableEq, Repr

def appStream : StreamCodec App :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat
      (StreamCodec.product intStream
        (StreamCodec.product intStream
          (StreamCodec.product intStream
            (StreamCodec.product digestStream
            (StreamCodec.product digestStream
              (StreamCodec.product StreamCodec.nat
                (StreamCodec.product StreamCodec.nat
                  (StreamCodec.product digestStream
                    CredentialAuthorityEntryCodec.capabilityIdStream))))))))))
    (fun app => (app.resource, app.packageManifest, app.generation, app.packageVersion,
      app.snapshotVersion, app.packageRoot, app.manifestRoot, app.interfaceId,
      app.interfaceVersion, app.interfaceRoot, app.capability))
    (fun (resource, packageManifest, generation, packageVersion, snapshotVersion, packageRoot, manifestRoot,
          interfaceId, interfaceVersion, interfaceRoot, capability) =>
      ⟨resource, packageManifest, generation, packageVersion, snapshotVersion, packageRoot, manifestRoot,
        interfaceId, interfaceVersion, interfaceRoot, capability⟩)
    (by intro app; cases app; rfl)

/-- Session identity and its selected current capability. The capability ID
is only a selector; special admission must check its current lineage and law. -/
structure Session where
  kind : InterfaceKind
  resource : Nat
  appResource : Nat
  appGeneration : Int
  generation : Int
  subject : SubjectId
  capability : CapabilityId
  origin : Origin
  deriving DecidableEq, Repr

def sessionStream : StreamCodec Session :=
  StreamCodec.xmap
    (StreamCodec.product interfaceKindStream
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product StreamCodec.nat
          (StreamCodec.product intStream
            (StreamCodec.product intStream
          (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
            (StreamCodec.product CredentialAuthorityEntryCodec.capabilityIdStream originStream)))))))
    (fun session => (session.kind, session.resource, session.appResource,
      session.appGeneration, session.generation,
      session.subject, session.capability, session.origin))
    (fun (kind, resource, appResource, appGeneration, generation, subject, capability, origin) =>
      ⟨kind, resource, appResource, appGeneration, generation, subject, capability, origin⟩)
    (by intro session; cases session; rfl)

/-- `generated` separates a trusted adapter-added header from untrusted
browser/API input. Admission must construct and compare generated values;
the tag alone is not evidence. Order and duplicate names are retained. -/
structure Header where
  name : List UInt8
  value : List UInt8
  generated : Bool
  deriving DecidableEq, Repr

def headerStream : StreamCodec Header :=
  StreamCodec.xmap
    (StreamCodec.product bytesStream
      (StreamCodec.product bytesStream StreamCodec.bool))
    (fun header => (header.name, header.value, header.generated))
    (fun (name, value, generated) => ⟨name, value, generated⟩)
    (by intro header; cases header; rfl)

/-- The complete app-visible HTTP request. No method is classified as read
here. The body is retained exactly; future streaming must add a separately
verified content-addressed handoff rather than relying on an asserted hash. -/
structure Request where
  operationId : Nat
  method : List UInt8
  path : List UInt8
  query : List UInt8
  headers : List Header
  body : List UInt8
  deriving DecidableEq, Repr

def requestStream : StreamCodec Request :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product bytesStream
        (StreamCodec.product bytesStream
          (StreamCodec.product bytesStream
            (StreamCodec.product (StreamCodec.list headerStream) bytesStream)))))
    (fun request => (request.operationId, request.method, request.path,
      request.query, request.headers, request.body))
    (fun (operationId, method, path, query, headers, body) =>
      ⟨operationId, method, path, query, headers, body⟩)
    (by intro request; cases request; rfl)

/-- Transport digest of the exact canonical method, path, query, ordered
ordinary headers (including cookies), and full body. Placing it at the codec
layer lets paid reserve signing bind this request before any replay-dependent
projection is built. -/
def requestDigest (request : Request) : Digest :=
  (Sp800185Cshake256.hash
    "DREGG/APPLICATION/PHYSICAL-WEB-REQUEST/v1".toUTF8.toList
    (requestStream.encode request)).digest

/-- App-facing identity and permission bitset. The received bytes are not a
decision: special admission must derive these from the current governed
participant grant, session policy and installed interface schema. -/
structure Identity where
  principal : List UInt8
  permissionSchemaRoot : Digest
  permissionBits : Nat
  deriving DecidableEq, Repr

def identityStream : StreamCodec Identity :=
  StreamCodec.xmap
    (StreamCodec.product bytesStream
      (StreamCodec.product digestStream StreamCodec.nat))
    (fun identity => (identity.principal, identity.permissionSchemaRoot,
      identity.permissionBits))
    (fun (principal, permissionSchemaRoot, permissionBits) =>
      ⟨principal, permissionSchemaRoot, permissionBits⟩)
    (by intro identity; cases identity; rfl)

structure Dispatch where
  app : App
  session : Session
  identity : Identity
  request : Request
  deriving DecidableEq, Repr

def dispatchStream : StreamCodec Dispatch :=
  StreamCodec.xmap
    (StreamCodec.product appStream
      (StreamCodec.product sessionStream
        (StreamCodec.product identityStream requestStream)))
    (fun dispatch => (dispatch.app, dispatch.session, dispatch.identity, dispatch.request))
    (fun (app, session, identity, request) => ⟨app, session, identity, request⟩)
    (by intro dispatch; cases dispatch; rfl)

private def frame : List UInt8 :=
  "DREGG/APPLICATION/DISPATCH-REQUEST/v1".toUTF8.toList

private def rawCodec : LawfulCodec Dispatch where
  encode dispatch := frame ++ dispatchStream.encode dispatch
  decode bytes := if bytes.take frame.length = frame then
    dispatchStream.toLawful.decode (bytes.drop frame.length) else none
  decode_encode := by
    intro dispatch
    have decoded := dispatchStream.toLawful.decode_encode dispatch
    change dispatchStream.toLawful.decode (dispatchStream.encode dispatch) = some dispatch at decoded
    simp [decoded]

def codec : LawfulCodec Dispatch := ResourceBirthCodec.strictCodec rawCodec

def Dispatch.canonicalBytes (dispatch : Dispatch) : List UInt8 :=
  codec.encode dispatch

theorem decode_encode (dispatch : Dispatch) :
    codec.decode dispatch.canonicalBytes = some dispatch := codec.decode_encode dispatch

theorem decoded_canonical {bytes : List UInt8} {dispatch : Dispatch}
    (decoded : codec.decode bytes = some dispatch) :
    dispatch.canonicalBytes = bytes :=
  ResourceBirthCodec.strictCodec_canonical rawCodec decoded

end Minidregg.Kernel.ApplicationDispatchCodec
