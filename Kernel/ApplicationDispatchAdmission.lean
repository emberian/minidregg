/-
Current-image selectors for special application dispatch. These helpers do not
admit a request by themselves: the receiver must check signed observations,
the DRC invocation, accepted historical share issuance, and one durable CAS.
-/
module

public import Effects.Revival.HostedDav
public import Effects.Revival.HostedConversation
public import Kernel.ApplicationDispatchAdmissionIngress
public import Kernel.ApplicationDispatchManifest
public import Kernel.ApplicationDispatchWitness
public import Kernel.ApplicationDispatchAuthority
public import Kernel.ApplicationShareIssueSource
public import Kernel.ResourceObservationAdmission
public import Kernel.PhysicalResourceReadGuard

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
import all Init.System.ST
import all Init.System.IO

@[expose] public section

namespace Minidregg.Kernel.ApplicationDispatchAdmission

open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.CredentialAuthorityPolicyRegistry
open Minidregg.Compiler.CredentialAuthorityDomain
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.IntStream (intStream)
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.ApplicationDispatchCodec
open Minidregg.Kernel.ApplicationDispatchCommand
open Minidregg.Kernel.ApplicationDispatchAdmissionIngress
open Minidregg.Kernel.ApplicationShareIssueSource

set_option autoImplicit false

abbrev Deployment := CanonicalCellRegistry.Deployment
abbrev Durable := DeclaredResourceController.Durable
abbrev Ground := DeclaredResourceController.Ground
abbrev Ambient := DeclaredResourceController.Ambient

/-- Stable 32-byte Sandstorm-facing identity for one Mini subject within one
app. Session reconnect, ticket replacement and app wake do not change it.
Display names are never inputs to this authority identity. -/
def principalFor (domain : Digest) (app : Nat) (subject : SubjectId) : List UInt8 :=
  (Sp800185Cshake256.hash
    "DREGG/APPLICATION/SANDSTORM-PRINCIPAL/v1".toUTF8.toList
    ((StreamCodec.product digestStream
      (StreamCodec.product StreamCodec.nat
        TypedAuthorizationRequestCodec.subjectIdStream)).encode
      (domain, app, subject))).bytes

theorem principalFor_length (domain : Digest) (app : Nat) (subject : SubjectId) :
    (principalFor domain app subject).length = 32 := by
  simp [principalFor, Sp800185Cshake256.hash]

/-- No caller may choose app-visible identity bytes or attach a session to a
different app/generation than the selected serving app. -/
def identityMatches (ingress : ApplicationDispatchAdmissionIngress.Ingress) : Bool :=
  ingress.dispatch.dispatch.identity.principal ==
      principalFor ingress.dispatch.domain ingress.dispatch.dispatch.app.resource
        ingress.dispatch.dispatch.session.subject &&
    decide (ingress.dispatch.dispatch.session.appResource =
      ingress.dispatch.dispatch.app.resource) &&
    decide (ingress.dispatch.dispatch.session.appGeneration =
      ingress.dispatch.dispatch.app.generation)

/-- Recover only selector coordinates from the canonical signed command.
`matchesCommand` and ordinary DRC admission must then check every byte and
current old page. An absent session observation capability refuses. -/
def selectCommand (ingress : ApplicationDispatchAdmissionIngress.Ingress) :
    Option Selection := do
  let signed ← DeclaredResourceController.commandCodec.decode
    ingress.dispatch.signed.commandBytes
  let first ← signed.targets.head?
  let observe ← first.observeCapability
  some ⟨first.expectedTargetRoot, observe⟩

def appState (app : Nat) (cell : PackedCell CanonicalCellRegistry.registry) :
    Option ApplicationGrain.State := do
  match cell with
  | ⟨.declaredObject, payload⟩ =>
      let page := payload.logical
      ApplicationGrain.readState app page
  | _ => none

def installedManifest (domain : Digest) (manifestResource app : Nat)
    (version : Int) (cell : PackedCell CanonicalCellRegistry.registry) :
    Option ApplicationDispatchManifest.Manifest := do
  match cell with
  | ⟨.content, payload⟩ =>
      let page := payload.logical
      ApplicationDispatchManifest.decodeInstalled domain manifestResource app version page
  | _ => none

def installedEnrollment (domain : Digest) (descriptorResource session : Nat)
    (generation : Int) (cell : PackedCell CanonicalCellRegistry.registry) :
    Option ApplicationGrainSessionEnrollment.Enrollment := do
  match cell with
  | ⟨.content, payload⟩ =>
      let page := payload.logical
      ApplicationGrainSessionEnrollment.decodeInstalled domain descriptorResource session
        generation page
  | _ => none

def installedTicket (domain : Digest) (ticketResource : Nat)
    (cell : PackedCell CanonicalCellRegistry.registry) :
    Option ApplicationDispatchAuthority.Ticket := do
  match cell with
  | ⟨.content, payload⟩ =>
      let page := payload.logical
      ApplicationDispatchAuthority.decodeInstalled domain ticketResource page
  | _ => none

/-- Ordinary client headers that the physical Sandstorm adapter may map to
WebRequest context. App identity and permission headers are absent here and
must be generated from the checked projection after durable admission. -/
def ordinaryHeaderName (name : List UInt8) : Bool :=
  (["cookie", "accept", "accept-encoding", "content-type", "user-agent",
    "if-match", "if-none-match", "x-requested-with", "x-csrftoken",
    "x-csrf-token", "oc-total-length", "oc-chunk-size", "x-oc-mtime",
    "oc-fileid", "oc-chunked", "oc-checksum", "oc-chunk-offset",
    "oc-lazyops", "content-encoding", "referer"] : List String).any (fun allowed => name == allowed.toUTF8.toList)

/-- A `referer` a signed request may carry is the path of a page of the grain's own origin and nothing else:
it starts with one `/` (not `//`, which is a network-path reference naming another origin) and has no
backslash. A cross-origin referer can leak a capability URL (Sandstorm strips it for that reason), so the
sender reduces a same-origin one to its path and drops any other; a signed request that still carries a
non-path referer is refused here. -/
def refererValueOk (value : List UInt8) : Bool :=
  value.head? == some 47 && (value.drop 1).head? != some 47 && !value.contains 92

/-- An ordinary header is admitted by name, and a `referer` additionally by value. -/
def ordinaryHeaderOk (name value : List UInt8) : Bool :=
  ordinaryHeaderName name && (name != "referer".toUTF8.toList || refererValueOk value)

theorem referer_is_ordinary : ordinaryHeaderName "referer".toUTF8.toList = true := by
  decide +kernel

/-- Teeth: a same-origin path is admitted; an absolute URL, a network-path reference, a path with a
backslash and the empty value are each refused. -/
theorem referer_value_path_only :
    refererValueOk "/page?x=1".toUTF8.toList = true ∧
    refererValueOk "https://other.example/page".toUTF8.toList = false ∧
    refererValueOk "//other.example/page".toUTF8.toList = false ∧
    refererValueOk "/a\\b".toUTF8.toList = false ∧
    refererValueOk [] = false := by
  decide +kernel

theorem ordinaryHeaderOk_referer_cross_origin_refused :
    ordinaryHeaderOk "referer".toUTF8.toList "https://other.example/".toUTF8.toList = false := by
  decide +kernel

/-- Off `referer` the value adds nothing: `ordinaryHeaderOk` is the name check. -/
theorem ordinaryHeaderOk_of_other (name value : List UInt8)
    (h : name ≠ "referer".toUTF8.toList) :
    ordinaryHeaderOk name value = ordinaryHeaderName name := by
  have hne : (name != "referer".toUTF8.toList) = true := bne_iff_ne.mpr h
  unfold ordinaryHeaderOk
  rw [hne]
  simp

def cleanTransportText (bytes : List UInt8) : Bool :=
  (String.fromUTF8? bytes.toByteArray).isSome &&
    bytes.all (fun byte => byte != 0 && byte != 10 && byte != 13)

/-- The WebSession method a streamed dispatch reaches: `openWebSocket`
(`web-session.capnp` @2). The Mini write is the open; the frames that follow
are physical bytes inside the admitted session, like a streamed body, and a
close writes nothing. It is a method token of its own so a committed record
says which WebSession call it admitted: an audit tells a socket open from a
`GET` by the record alone. -/
def streamedOpenMethod : List UInt8 := "WEBSOCKET".toUTF8.toList

/-- The one header a streamed open carries beyond the ordinary set: the
client's requested subprotocols, delivered as `openWebSocket`'s `protocol`
list. It is signed like every other app-visible input. -/
def webSocketProtocolHeader : List UInt8 := "sec-websocket-protocol".toUTF8.toList

/-- A committed request is a streamed dispatch exactly when it names the
streamed-open method. -/
def streamed (request : ApplicationDispatchCodec.Request) : Bool :=
  request.method == streamedOpenMethod

/-- The WebDAV and CalDAV calls a WebSession serves beyond the plain exchanges
(`web-session.capnp` `propfind` @7, `proppatch` @8, `mkcol` @9, `copy` @10, `move` @11,
`lock` @12, `unlock` @13, `report` @15, `options` @16). `acl` @14 is absent: no
admitted app uses it, and an absent method is refused before any record. Each is an
ordinary exchange: one request, one response, one Mini write. -/
def davMethod (method : List UInt8) : Bool :=
  (["PROPFIND", "PROPPATCH", "MKCOL", "COPY", "MOVE", "LOCK", "UNLOCK", "REPORT",
    "OPTIONS"] : List String).any (fun allowed => method == allowed.toUTF8.toList)

/-- The request headers a DAV call carries as its typed parameters: `depth` (propfind's
`depth`, copy's and lock's `shallow`), `destination` (copy and move), `overwrite`
(`noOverwrite`) and `lock-token` (unlock). They are signed like ordinary headers and admitted
only on a DAV method: on every other request they are refused. -/
def davHeaderName (name : List UInt8) : Bool :=
  (["depth", "destination", "overwrite", "lock-token"] : List String).any
    (fun allowed => name == allowed.toUTF8.toList)

/-- DAV calls whose WebSession method has no content parameter. -/
def davBodyless (method : List UInt8) : Bool :=
  (["COPY", "MOVE", "UNLOCK", "OPTIONS"] : List String).any
    (fun allowed => method == allowed.toUTF8.toList)

/-- DAV calls whose content is `xmlContent :Text`: the body must be UTF-8 text without NUL. -/
def davTextBody (method : List UInt8) : Bool :=
  (["PROPFIND", "PROPPATCH", "LOCK"] : List String).any
    (fun allowed => method == allowed.toUTF8.toList)

def exchangeMethod (method : List UInt8) : Bool :=
  (["GET", "HEAD", "POST", "PUT", "PATCH", "DELETE"] : List String).any
    (fun allowed => method == allowed.toUTF8.toList) || davMethod method || method == Effects.Revival.HostedConversation.method

/-- The exact signed request is a bounded WebSession candidate. The received
`generated` tag is never trusted: every incoming header must be ordinary,
and the host synthesizes Sandstorm security context from checked fields.
This excludes unsafe or unsupported HTTP shapes before a pending event.
`streamedOpen` says whether this route may admit a streamed open at all; a
streamed open carries no body and is otherwise held to a `GET`'s shape. -/
def requestSafeFor (streamedOpen : Bool) (request : ApplicationDispatchCodec.Request) : Bool :=
  let methodAllowed :=
    exchangeMethod request.method || (streamedOpen && streamed request)
  let bodyAllowed :=
    if request.method == "GET".toUTF8.toList ||
        request.method == "HEAD".toUTF8.toList ||
        request.method == "DELETE".toUTF8.toList ||
        streamed request || davBodyless request.method then
      request.body.isEmpty
    else if request.method == Effects.Revival.HostedConversation.method then
      Effects.Revival.HostedConversation.descriptorSafe request.body
    else if davTextBody request.method then
      (String.fromUTF8? request.body.toByteArray).isSome && !request.body.contains 0
    else true
  methodAllowed && bodyAllowed &&
    decide (request.path.length + request.query.length ≤ 8192) &&
    decide (request.body.length ≤ 8 * 1024 * 1024) &&
    decide (request.headers.length ≤ 128) &&
    request.path.head? != some 47 &&
    !(request.path ++ request.query).contains 35 &&
    !request.path.contains 63 &&
    cleanTransportText request.path && cleanTransportText request.query &&
    request.headers.all (fun header =>
      !header.generated &&
      (ordinaryHeaderOk header.name header.value ||
        (streamed request && header.name == webSocketProtocolHeader) ||
        (davMethod request.method &&
          Effects.Revival.HostedDav.headerAllowed request.method header.name header.value)) &&
      decide (header.name.length ≤ 128) &&
      decide (header.value.length ≤ 8192) &&
      cleanTransportText header.value)

/-- The exchange-only shape: every route that may not open a stream (the
agent and lifetime dispatch paths) admits exactly what it admitted before
streamed opens existed. -/
def requestSafe (request : ApplicationDispatchCodec.Request) : Bool :=
  requestSafeFor false request

/-- A human session's dispatch may be a streamed open; an agent-origin one
may not (an agent's lifetime fence has no socket to close). -/
def dispatchRequestSafe (dispatch : ApplicationDispatchCodec.Dispatch) : Bool :=
  requestSafeFor (dispatch.session.origin == .human) dispatch.request

theorem streamedOpenMethod_not_exchange : exchangeMethod streamedOpenMethod = false := by
  decide +kernel

theorem webSocketProtocolHeader_not_ordinary :
    ordinaryHeaderName webSocketProtocolHeader = false := by
  decide +kernel

/-- The `GET` method token, the exchange a streamed open is compared with. -/
def getMethod : List UInt8 := "GET".toUTF8.toList

theorem getMethod_exchange : exchangeMethod getMethod = true := by
  decide +kernel

theorem getMethod_not_streamed : (getMethod == streamedOpenMethod) = false := by
  decide +kernel

theorem davMethod_streamedOpen : davMethod streamedOpenMethod = false := by
  decide +kernel

theorem davMethod_get : davMethod getMethod = false := by
  decide +kernel

/-! ### The DAV calls: admitted exactly as `requestSafeFor` says, with poles

Statement: a DAV method is an ordinary exchange (`exchangeMethod`), its typed parameters
travel as the four DAV headers and nowhere else, a parameter-only call carries no body, and
an `xmlContent` call carries UTF-8 text. The theorems below are the general facts; the
`#guard`-style examples after them are the satisfiable witnesses and the poles (each a
concrete request, decided by the kernel). -/

/-- Opening DAV changes nothing for a non-DAV request carrying no DAV header: the admission is
the same Boolean with the DAV disjuncts erased. -/
theorem dav_header_needs_dav_method (open_ : Bool) (request : ApplicationDispatchCodec.Request)
    (hdav : davMethod request.method = false)
    (header : ApplicationDispatchCodec.Header) (mem : header ∈ request.headers)
    (hname : ordinaryHeaderOk header.name header.value = false)
    (hproto : streamed request = false ∨ header.name ≠ webSocketProtocolHeader) :
    requestSafeFor open_ request = false := by
  simp only [requestSafeFor, hdav, Bool.false_and, Bool.or_false]
  rw [Bool.eq_false_iff]
  intro safe
  simp only [Bool.and_eq_true, List.all_eq_true] at safe
  have h := (safe.2 header mem).1.1.1.2
  rcases hproto with hs | hn
  · simp [hname, hs] at h
  · simp [hname, hn] at h

/-- A DAV call without a content parameter (COPY, MOVE, UNLOCK, OPTIONS) carries no body. -/
theorem dav_bodyless_body_empty (open_ : Bool) (request : ApplicationDispatchCodec.Request)
    (safe : requestSafeFor open_ request = true) (h : davBodyless request.method = true) :
    request.body = [] := by
  simp [requestSafeFor, h] at safe
  tauto

/-- The DAV parameter headers are never ordinary headers: off a DAV method each is refused. -/
theorem davHeaderNames_not_ordinary :
    (["depth", "destination", "overwrite", "lock-token"] : List String).all
      (fun name => !ordinaryHeaderName name.toUTF8.toList &&
        name.toUTF8.toList != webSocketProtocolHeader) = true := by
  decide +kernel

/-- Every DAV method is an exchange and none is a streamed open. -/
theorem davMethods_exchange :
    (["PROPFIND", "PROPPATCH", "MKCOL", "COPY", "MOVE", "LOCK", "UNLOCK", "REPORT",
      "OPTIONS"] : List String).all
      (fun m => exchangeMethod m.toUTF8.toList && m.toUTF8.toList != streamedOpenMethod) = true := by
  decide +kernel

/-- A request fixture: a method, a path, headers and a body. -/
def davFixture (method : String) (headers : List (String × String)) (body : String) :
    ApplicationDispatchCodec.Request :=
  { operationId := 1, method := method.toUTF8.toList, path := "dav/notes".toUTF8.toList,
    query := [], body := body.toUTF8.toList,
    headers := headers.map fun (n, v) =>
      { name := n.toUTF8.toList, value := v.toUTF8.toList, generated := false } }

/-- Satisfiable: a PROPFIND with `depth: 1` and an XML body is admitted, on a human route and
on an agent route alike. -/
theorem dav_propfind_admitted :
    requestSafeFor false (davFixture "PROPFIND" [("depth", "1"), ("content-type", "application/xml")]
      "<?xml version=\"1.0\"?><propfind xmlns=\"DAV:\"><allprop/></propfind>") = true := by
  decide +kernel

/-- Satisfiable: MKCOL, a MOVE with its destination and overwrite, a REPORT with a body. -/
theorem dav_write_calls_admitted :
    requestSafeFor false (davFixture "MKCOL" [] "") = true ∧
    requestSafeFor false (davFixture "MOVE"
      [("destination", "https://g.example/dav/old"), ("overwrite", "F")] "") = true ∧
    requestSafeFor true (davFixture "REPORT" [("depth", "1")] "<calendar-query/>") = true := by
  decide +kernel

/-- Poles: a GET with a DAV header, a COPY with a body, an ACL, and a PROPFIND whose body is
not UTF-8 are each refused. -/
theorem dav_poles :
    requestSafeFor true (davFixture "GET" [("depth", "1")] "") = false ∧
    requestSafeFor true (davFixture "COPY" [("destination", "https://g.example/x")] "body") = false ∧
    requestSafeFor true (davFixture "ACL" [] "<acl/>") = false ∧
    requestSafeFor true
      { davFixture "PROPFIND" [("depth", "0")] "" with body := [0xff, 0xfe] } = false := by
  decide +kernel

/-- Pole: a route that may not open a stream refuses every streamed open. -/
theorem requestSafe_refuses_streamed (request : ApplicationDispatchCodec.Request)
    (h : streamed request = true) : requestSafe request = false := by
  have hm : request.method = streamedOpenMethod := by
    simpa [streamed] using h
  simp [requestSafe, requestSafeFor, hm, streamedOpenMethod_not_exchange]

/-- An agent-origin dispatch never admits a streamed open. -/
theorem dispatchRequestSafe_agent_refuses_streamed
    (dispatch : ApplicationDispatchCodec.Dispatch) (task : Nat) (generation : Int)
    (origin : dispatch.session.origin = .agent task generation)
    (h : streamed dispatch.request = true) : dispatchRequestSafe dispatch = false := by
  have hfalse : (dispatch.session.origin == Origin.human) = false := by
    rw [origin]; rfl
  simp only [dispatchRequestSafe, hfalse]
  exact requestSafe_refuses_streamed dispatch.request h

/-- Opening streams changes nothing for an exchange: on every non-streamed
request the human shape is exactly the exchange-only shape. -/
theorem requestSafeFor_exchange (open_ : Bool) (request : ApplicationDispatchCodec.Request)
    (h : streamed request = false) : requestSafeFor open_ request = requestSafe request := by
  simp [requestSafe, requestSafeFor, h]

/-- A streamed open carries no body. -/
theorem streamed_open_body_empty (open_ : Bool) (request : ApplicationDispatchCodec.Request)
    (safe : requestSafeFor open_ request = true) (h : streamed request = true) :
    request.body = [] := by
  simp [requestSafeFor, h] at safe
  tauto

/-- The same admission a `GET` gets: a streamed open with no subprotocol
header is safe on a human route exactly when the same request as a `GET` is
safe. Only the method token differs between the two records. -/
theorem streamed_open_shape_is_get_shape (request : ApplicationDispatchCodec.Request)
    (h : streamed request = true)
    (noProtocol : ∀ header ∈ request.headers, header.name ≠ webSocketProtocolHeader) :
    requestSafeFor true request = requestSafe { request with method := getMethod } := by
  have hget : streamed { request with method := getMethod } = false := by
    simpa [streamed] using getMethod_not_streamed
  have hm : request.method = streamedOpenMethod := by
    simpa [streamed] using h
  have hGetBody : (getMethod == "GET".toUTF8.toList) = true := by
    simp [getMethod]
  rw [Bool.eq_iff_iff]
  simp only [requestSafe, requestSafeFor, hget, h, hm, getMethod_exchange, hGetBody,
    streamedOpenMethod_not_exchange, davMethod_streamedOpen, davMethod_get]
  simp only [Bool.or_true, Bool.true_or, Bool.and_true, Bool.true_and,
    Bool.false_and, Bool.or_false, ↓reduceIte]
  simp only [Bool.and_eq_true, List.all_eq_true]
  refine and_congr Iff.rfl (forall₂_congr fun header mem => ?_)
  have hne : (header.name == webSocketProtocolHeader) = false := by
    simpa using noProtocol header mem
  simp [hne]

#assert_axioms streamedOpenMethod_not_exchange
#assert_axioms webSocketProtocolHeader_not_ordinary
#assert_axioms requestSafe_refuses_streamed
#assert_axioms dispatchRequestSafe_agent_refuses_streamed
#assert_axioms requestSafeFor_exchange
#assert_axioms dav_header_needs_dav_method
#assert_axioms dav_bodyless_body_empty
#assert_axioms davHeaderNames_not_ordinary
#assert_axioms davMethods_exchange
#assert_axioms dav_propfind_admitted
#assert_axioms dav_write_calls_admitted
#assert_axioms dav_poles
#assert_axioms streamed_open_body_empty
#assert_axioms streamed_open_shape_is_get_shape

/-- A separate current native observation request for each read-only resource.
The source command is the DRC session/agent witness, while the native observe
signature is bound to the current root, policy epoch and immutable context. -/
def observationRequest {F : Type} [Field F]
    (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (ground : Ground deployment)
    (ingress : ApplicationDispatchAdmissionIngress.Ingress)
    (selection : Selection)
    (prepared : DeclaredResourceController.PreparedInvocation deployment profile ambient ground
      (command ingress.dispatch selection ingress.parent))
    (resource : Nat) (capability : CapabilityId) (root : Digest) : Request .object :=
  let target : DeclaredResourceController.Target :=
    ⟨.object, resource, capability, 1, root, .content ⟨[]⟩, none, none, none⟩
  { DeclaredResourceController.requestFor ground.authority profile.semantics
      ambient (command ingress.dispatch selection ingress.parent) target root with
    verb := .observeObject }

def observationGuard (resource : Nat) (root : Digest) : ReadGuard :=
  ⟨⟨resource⟩, root⟩

/-- A signed observation names the inner payload root. A durable CAS guard
protects the complete encoded physical cell, whose root is generally distinct. -/
theorem observedPhysicalRoot_current {deployment : Deployment}
    (context : ResourceObservationAdmission.Context deployment)
    (resource : Nat) (packed : PackedCell CanonicalCellRegistry.registry)
    (present : context.directory.slots resource = .present packed) :
    ResourceBirthCodec.physicalRoot (.live packed) =
      context.view.model.roots ⟨resource⟩ :=
  ServedBasis.Ground.physicalCurrent context resource packed present

/-- Native observation signatures bind the base signed request and the
selected issue/ticket coordinates, without including their own envelopes. -/
def observationContext (ingress : ApplicationDispatchAdmissionIngress.Ingress) :
    List UInt8 :=
  "DREGG/APPLICATION/DISPATCH-OBSERVATION/v7".toUTF8.toList ++
    ((StreamCodec.product digestStream
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
          (StreamCodec.product digestStream
            (StreamCodec.product CredentialAuthorityEntryCodec.capabilityIdStream
              bytesStream))))).encode
      (ApplicationDispatchIngress.requestDigest ingress.dispatch,
        ingress.appSnapshotManifest, ingress.appManagementSubject,
        ingress.ticketRoot, ingress.ticketObserveCapability,
        ingress.issueIngressBytes))

def observationMarker
    (ingress : ApplicationDispatchAdmissionIngress.Ingress)
    (selection : Selection) : Nat :=
  DeclaredResourceController.operationMarker ingress.dispatch.domain
    ingress.dispatch.semantics (command ingress.dispatch selection ingress.parent)

structure CheckedRead {F : Type} [Field F] [DecidableEq F]
    (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (ground : Ground deployment)
    (ingress : ApplicationDispatchAdmissionIngress.Ingress)
    (selection : Selection)
    (prepared : DeclaredResourceController.PreparedInvocation deployment profile ambient ground
      (command ingress.dispatch selection ingress.parent))
    (resource : Nat) (capability : CapabilityId) (root : Digest)
    (envelope : List UInt8) where
  private mk ::
  selected : ResourceObservationAdmission.Prepared
    (DeclaredResourceController.readContext prepared) profile
    (observationRequest deployment profile ambient ground ingress selection prepared
      resource capability root)
    (observationMarker ingress selection) capability (observationContext ingress)
  checked : ResourceObservationAdmission.Checked selected envelope
  current : ResourceBirthCodec.physicalRoot (.live selected.observed.before) =
    ground.view.model.roots ⟨resource⟩
  readonly : (observationGuard resource
    (ResourceBirthCodec.physicalRoot (.live selected.observed.before))).cellId ∉
    (DeclaredResourceController.writes prepared).map DataWrite.cellId

/-- The same checked read retains the signed inner commitment. It is not
substituted for the physical root used by the later CAS read guard. -/
theorem CheckedRead.signedInnerRoot {F : Type} [Field F] [DecidableEq F]
    {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : Ambient} {ground : Ground deployment}
    {ingress : ApplicationDispatchAdmissionIngress.Ingress}
    {selection : Selection}
    {prepared : DeclaredResourceController.PreparedInvocation deployment profile ambient ground
      (command ingress.dispatch selection ingress.parent)}
    {resource : Nat} {capability : CapabilityId} {root : Digest}
    {envelope : List UInt8}
    (read : CheckedRead deployment profile ambient ground ingress selection prepared
      resource capability root envelope) :
    root = read.selected.observed.before.payload.root :=
  ResourceObservationAdmission.preparation_actual_root read.selected
/-- The checked read quotes the signed root, is the ground's current cell at the
resource, and is not written by the prepared invocation. -/
theorem CheckedRead.sound {F : Type} [Field F] [DecidableEq F]
    {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : Ambient} {ground : Ground deployment}
    {ingress : ApplicationDispatchAdmissionIngress.Ingress}
    {selection : Selection}
    {prepared : DeclaredResourceController.PreparedInvocation deployment profile ambient ground
      (command ingress.dispatch selection ingress.parent)}
    {resource : Nat} {capability : CapabilityId} {root : Digest}
    {envelope : List UInt8}
    (read : CheckedRead deployment profile ambient ground ingress selection prepared
      resource capability root envelope) :
    root = read.selected.observed.before.payload.root ∧
      ResourceBirthCodec.physicalRoot (.live read.selected.observed.before) =
        ground.view.model.roots ⟨resource⟩ ∧
      (observationGuard resource
          (ResourceBirthCodec.physicalRoot (.live read.selected.observed.before))).cellId ∉
        (DeclaredResourceController.writes prepared).map DataWrite.cellId :=
  ⟨read.signedInnerRoot, read.current, read.readonly⟩

def checkRead {F : Type} [Field F] [DecidableEq F]
    (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (native : CredentialSignatureIO.NativeConfig)
    (ground : Ground deployment) (ingress : ApplicationDispatchAdmissionIngress.Ingress)
    (selection : Selection)
    (prepared : DeclaredResourceController.PreparedInvocation deployment profile ambient ground
      (command ingress.dispatch selection ingress.parent))
    (resource : Nat) (capability : CapabilityId) (root : Digest)
    (envelope : List UInt8) :
    IO (Except String (CheckedRead deployment profile ambient ground ingress selection
      prepared resource capability root envelope)) := do
  let wanted := observationRequest deployment profile ambient ground ingress selection
    prepared resource capability root
  let context := DeclaredResourceController.readContext prepared
  match ResourceObservationAdmission.prepare context profile wanted
      (observationMarker ingress selection) capability (observationContext ingress) with
  | .error _ => return .error "current application observation refused"
  | .ok selected =>
      match ← ResourceObservationAdmission.check native selected envelope with
      | .error _ => return .error "signed application observation refused"
      | .ok checked =>
          let current := observedPhysicalRoot_current context resource
            selected.observed.before selected.observed.present
          if readonly : (observationGuard resource
              (ResourceBirthCodec.physicalRoot (.live selected.observed.before))).cellId ∉
              (DeclaredResourceController.writes prepared).map DataWrite.cellId then
            return .ok ⟨selected, checked, current, readonly⟩
          else return .error "application observation overlaps dispatch writes"

/-- Exact meaning extracted from four current, independently observed cells.
The share ceiling is app-issued, while the participant's enrollment requests
the role. Neither the HTTP method nor a display label grants a bit. -/
def selectedMeaning (ingress : ApplicationDispatchAdmissionIngress.Ingress)
    (spec : Spec) (actualApp : ApplicationGrain.State)
    (manifest : ApplicationDispatchManifest.Manifest)
    (enrollment : ApplicationGrainSessionEnrollment.Enrollment)
    (ticket : ApplicationDispatchAuthority.Ticket) : Option (List Bool) := do
  let dispatch := ingress.dispatch.dispatch
  if !identityMatches ingress ||
      !ApplicationDispatchWitness.matchesServing dispatch actualApp ||
      !ApplicationDispatchManifest.matchesDispatch manifest dispatch ||
      ticket != spec.ticket ||
      ticket.resource == dispatch.app.resource ||
      ticket.resource == ingress.dispatch.enrollmentResource ||
      ticket.participant.ticketObserveCapability != ingress.ticketObserveCapability ||
      dispatch.app.capability != ingress.dispatch.appObserveCapability then
    none
  else
    let interface ← manifest.select dispatch.app.interfaceId
    ApplicationDispatchAuthority.eligibleBits ticket dispatch enrollment interface.schema

/-- Live dispatch requires the current v2 app law. The exact v1 law remains
available for replay re-admission at a verifier-authenticated original prefix,
but must not turn a present v1 installation into a new live permit. -/
theorem current_app_policy_excludes_v1 (package snapshot : Nat)
    (management : Minidregg.Pred.Pred) :
    ApplicationGrain.policyV1 package snapshot management ≠
      ApplicationGrain.policy package snapshot management := by
  intro equal
  have lengthEqual := congrArg
    (fun policy : Minidregg.Pred.Pred =>
      match policy with
      | .anyL alternatives => alternatives.toList.length
      | _ => 0) equal
  simp [ApplicationGrain.policyV1, ApplicationGrain.policy,
    Minidregg.Pred.Pred.any] at lengthEqual

/-- Current app/package source laws are matched exactly. The standard family
binds share issuance to its management subject. The explicit managed family
names a member owner and a separate lifecycle manager in the app law; the
ticket's issuer is either of them, and the other is derived from current law.
Issuer delegation lineage is independently checked below; arbitrary
app-revised laws are not treated as these source families. Each clause is
named so a refusal can say which one failed. -/
def linkedCurrentPolicyClauses {F : Type} [Field F]
    (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (ground : Ground deployment)
    (ingress : ApplicationDispatchAdmissionIngress.Ingress)
    (spec : Spec) (selection : Selection)
    (prepared : DeclaredResourceController.PreparedInvocation deployment profile ambient ground
      (command ingress.dispatch selection ingress.parent)) : List (String × Bool) :=
  let auth := ground.authority.logical
  let directory := ground.directory
  let policyAt := fun target => do
    let head ← CredentialAuthorityDomain.headAt auth ⟨target⟩
    let policy ← CanonicalCellRegistry.loadPolicySource deployment.domain directory head.address
    if policy.record.policyId == ⟨target⟩ &&
        policy.record.version == head.version &&
        policy.record.semantics == profile.semantics then
      pure policy.record.predicate
    else none
  let app := ingress.dispatch.dispatch.app.resource
  let manifest := ingress.dispatch.dispatch.app.packageManifest
  let session := ingress.dispatch.dispatch.session.resource
  let descriptor := ingress.dispatch.enrollmentResource
  let kind := if ingress.dispatch.dispatch.session.kind = InterfaceKind.web then
    ApplicationGrainSession.Kind.web else ApplicationGrainSession.Kind.api
  let management := Minidregg.Pred.Pred.eq "request/subject" ingress.appManagementSubject.value
  let participant := ingress.dispatch.dispatch.session.subject
  -- The session and descriptor laws are exactly those the current session
  -- birth installs (`ApplicationGrainSessionBirth.Ready.policyRecords`):
  -- the participant manages its own session. Expecting the older no-manager
  -- law refused every dispatch for a currently born session.
  let sessionManagement := Minidregg.Pred.Pred.eq "request/subject" participant.value
  [("issuer-is-app-management-subject", decide (spec.issuer = ingress.appManagementSubject)),
   -- The ticket's issuer is either the app's sole management subject (the
   -- unmanaged law), the member owner of a managed app (its manager derived
   -- from the law), or the manager of a managed app (its owner derived from
   -- the law). The app delegation lineage is checked separately.
   ("app-and-package-law",
    (policyAt app == some (ApplicationGrain.policy manifest ingress.appSnapshotManifest management) &&
      policyAt manifest == some (ApplicationGrain.packageManifestPolicy app management)) ||
    ApplicationGrain.managedPoliciesMatchOwner app manifest ingress.appSnapshotManifest
      ingress.appManagementSubject.value (policyAt app) (policyAt manifest) ||
    ApplicationGrain.managedPoliciesMatch app manifest ingress.appSnapshotManifest
      ingress.appManagementSubject.value (policyAt app) (policyAt manifest)),
   ("session-law", policyAt session == some (ApplicationGrainSession.policy descriptor kind
      participant sessionManagement)),
   ("descriptor-law", policyAt descriptor == some (ApplicationGrainSession.descriptorPolicy session kind
      participant sessionManagement)),
   ("ticket-law", policyAt spec.ticket.resource == some (ticketPolicy spec.issuer))]

/-- All named clauses hold. -/
def linkedCurrentPolicies {F : Type} [Field F]
    (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (ground : Ground deployment)
    (ingress : ApplicationDispatchAdmissionIngress.Ingress)
    (spec : Spec) (selection : Selection)
    (prepared : DeclaredResourceController.PreparedInvocation deployment profile ambient ground
      (command ingress.dispatch selection ingress.parent)) : Bool :=
  (linkedCurrentPolicyClauses deployment profile ambient ground ingress spec selection
    prepared).all (·.2)

/-- The first failing clause's name, for a refusal that names what it refused. -/
def firstFailedLinkageClause {F : Type} [Field F]
    (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (ground : Ground deployment)
    (ingress : ApplicationDispatchAdmissionIngress.Ingress)
    (spec : Spec) (selection : Selection)
    (prepared : DeclaredResourceController.PreparedInvocation deployment profile ambient ground
      (command ingress.dispatch selection ingress.parent)) : Option String :=
  ((linkedCurrentPolicyClauses deployment profile ambient ground ingress spec selection
    prepared).find? (fun c => !c.2)).map (·.1)

/-- Issuance authenticated the issuer once. At each dispatch, the same
selected app-delegation capability must still be present with valid stored
lineage, current epochs, time window and no ancestor/channel revocation.
This is a data/current-law check; it does not pretend an old signature is a
fresh signature at the new height. The app law is separately exact-matched
by `linkedCurrentPolicies`. -/
def issuerLineageCurrentFromSourceBytes {F : Type} [Field F]
    (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (ground : Ground deployment)
    (ingress : ApplicationDispatchAdmissionIngress.Ingress)
    (spec : Spec) (selection : Selection)
    (originalSourceBytes : List UInt8)
    (prepared : DeclaredResourceController.PreparedInvocation deployment profile ambient ground
      (command ingress.dispatch selection ingress.parent)) : Bool :=
  let snapshot := ground.authority
  let request := ApplicationShareIssueSource.appRequestFromSourceBytes deployment.domain profile.semantics
    ambient.federation snapshot.authState ambient.height ingress.dispatch.appRoot spec originalSourceBytes
  match CredentialAuthorityState.readCapability snapshot.cell .object spec.appDelegateCapability with
  | none => false
  | some stored =>
      CredentialAuthorityPolicyRegistry.capabilityCheck snapshot stored.head
        (CredentialAuthorityPolicyRegistry.storedCapabilityDigest snapshot stored) &&
      AuthorizationDeclaration.capabilityAdmissibleCheck stored.head snapshot.authState request


def issuerLineageCurrent {F : Type} [Field F]
    (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (ground : Ground deployment)
    (ingress : ApplicationDispatchAdmissionIngress.Ingress)
    (spec : Spec) (selection : Selection)
    (descriptor : ResourceBirth.Descriptor CanonicalCellRegistry.registry)
    (prepared : DeclaredResourceController.PreparedInvocation deployment profile ambient ground
      (command ingress.dispatch selection ingress.parent)) : Bool :=
  issuerLineageCurrentFromSourceBytes deployment profile ambient ground ingress spec selection
    (ApplicationShareIssueSource.sourceBytes spec descriptor) prepared


/-- Current-image native checks, still short of accepted historical issue
provenance and a durable special pending event. The spec and original source
bytes must come from a verified historical issue selector, never directly
from HTTP or the caller's ticket bytes. -/
structure CheckedCurrentForSourceBytes {F : Type} [Field F] [DecidableEq F]
    (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (ground : Ground deployment)
    (ingress : ApplicationDispatchAdmissionIngress.Ingress)
    (spec : Spec) (originalSourceBytes : List UInt8) where
  private mk ::
  profileExact : ingress.dispatch.domain = deployment.domain ∧
    ingress.dispatch.semantics = profile.semantics
  identityExact : identityMatches ingress = true
  selection : Selection
  selectedCommand : selectCommand ingress = some selection
  signedCommand : DeclaredResourceController.Command
  decodedCommand : DeclaredResourceController.commandCodec.decode
    ingress.dispatch.signed.commandBytes = some signedCommand
  commandExact : matchesCommand ingress.dispatch selection ingress.parent signedCommand = true
  prepared : DeclaredResourceController.PreparedInvocation deployment profile ambient ground
    (command ingress.dispatch selection ingress.parent)
  shape : DeclaredResourceController.PhysicalShape prepared
  linked : linkedCurrentPolicies deployment profile ambient ground ingress spec selection prepared = true
  appRead : CheckedRead deployment profile ambient ground ingress selection prepared
    ingress.dispatch.dispatch.app.resource ingress.dispatch.appObserveCapability
    ingress.dispatch.appRoot ingress.dispatch.appObservationEnvelope
  manifestRead : CheckedRead deployment profile ambient ground ingress selection prepared
    ingress.dispatch.dispatch.app.packageManifest ingress.dispatch.manifestObserveCapability
    ingress.dispatch.dispatch.app.manifestRoot ingress.dispatch.manifestObservationEnvelope
  enrollmentRead : CheckedRead deployment profile ambient ground ingress selection prepared
    ingress.dispatch.enrollmentResource ingress.dispatch.enrollmentObserveCapability
    ingress.dispatch.enrollmentRoot ingress.dispatch.enrollmentObservationEnvelope
  ticketRead : CheckedRead deployment profile ambient ground ingress selection prepared
    spec.ticket.resource ingress.ticketObserveCapability ingress.ticketRoot
    ingress.ticketObservationEnvelope
  actualApp : ApplicationGrain.State
  appExact : appState ingress.dispatch.dispatch.app.resource appRead.selected.observed.before =
    some actualApp
  manifest : ApplicationDispatchManifest.Manifest
  manifestExact : installedManifest deployment.domain
    ingress.dispatch.dispatch.app.packageManifest ingress.dispatch.dispatch.app.resource
    ingress.dispatch.dispatch.app.packageVersion manifestRead.selected.observed.before =
      some manifest
  enrollment : ApplicationGrainSessionEnrollment.Enrollment
  enrollmentExact : installedEnrollment deployment.domain ingress.dispatch.enrollmentResource
    ingress.dispatch.dispatch.session.resource ingress.dispatch.dispatch.session.generation
    enrollmentRead.selected.observed.before = some enrollment
  ticket : ApplicationDispatchAuthority.Ticket
  ticketExact : installedTicket deployment.domain spec.ticket.resource
    ticketRead.selected.observed.before = some ticket
  ticketLive : ticket.liveAt ambient.height = true
  bits : List Bool
  meaningExact : selectedMeaning ingress spec actualApp manifest enrollment ticket = some bits
  requestShape : dispatchRequestSafe ingress.dispatch.dispatch = true
  issuerCurrent : issuerLineageCurrentFromSourceBytes deployment profile ambient ground ingress spec
    selection originalSourceBytes prepared = true
  invocation : DeclaredResourceController.AcceptedInvocation prepared ingress.dispatch.signed
/-- The current checks bind the ingress to the deployment profile, its signed command,
the live installed ticket of the spec, and the issuer lineage from the source bytes. -/
theorem CheckedCurrentForSourceBytes.sound {F : Type} [Field F] [DecidableEq F]
    {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : Ambient} {ground : Ground deployment}
    {ingress : ApplicationDispatchAdmissionIngress.Ingress}
    {spec : Spec} {originalSourceBytes : List UInt8}
    (checked : CheckedCurrentForSourceBytes deployment profile ambient ground ingress spec
      originalSourceBytes) :
    (ingress.dispatch.domain = deployment.domain ∧
        ingress.dispatch.semantics = profile.semantics) ∧
      matchesCommand ingress.dispatch checked.selection ingress.parent checked.signedCommand = true ∧
      installedTicket deployment.domain spec.ticket.resource
        checked.ticketRead.selected.observed.before = some checked.ticket ∧
      checked.ticket.liveAt ambient.height = true ∧
      issuerLineageCurrentFromSourceBytes deployment profile ambient ground ingress spec
        checked.selection originalSourceBytes checked.prepared = true :=
  ⟨checked.profileExact, checked.commandExact, checked.ticketExact, checked.ticketLive,
    checked.issuerCurrent⟩

/-- The original API remains definitionally the same admission over its own
canonical descriptor commitment. Carried users require separate provenance. -/
abbrev CheckedCurrent {F : Type} [Field F] [DecidableEq F]
    (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (ground : Ground deployment)
    (ingress : ApplicationDispatchAdmissionIngress.Ingress)
    (spec : Spec) (descriptor : ResourceBirth.Descriptor CanonicalCellRegistry.registry) :=
  CheckedCurrentForSourceBytes deployment profile ambient ground ingress spec
    (ApplicationShareIssueSource.sourceBytes spec descriptor)

/-- Only app-side identity and authorization continuity belongs in the
WebSession cache key. A DRC active witness reads the live session root on
every request; that workflow root, the HTTP request and app checkpoint
snapshot version must not recreate the app-side WebSession. -/
structure SessionFingerprintKey where
  authorityRoot : Digest
  app : ApplicationDispatchCodec.App
  session : ApplicationDispatchCodec.Session
  identity : ApplicationDispatchCodec.Identity
  bits : List Bool
  ticketResource : Nat
  ticketRoot : Digest
  enrollmentResource : Nat
  enrollmentRoot : Digest
  issueIngressBytes : List UInt8
  deriving DecidableEq

/-- `authorityRoot` is the authority root at admission (the prepared
invocation's snapshot); the signed command no longer names one. -/
def sessionFingerprintKey (authorityRoot : Digest) (selection : Selection)
    (dispatch : ApplicationDispatchCodec.Dispatch) (bits : List Bool)
    (ticketResource : Nat) (ticketRoot : Digest)
    (enrollmentResource : Nat) (enrollmentRoot : Digest)
    (issueIngressBytes : List UInt8) : SessionFingerprintKey :=
  ⟨authorityRoot, { dispatch.app with snapshotVersion := 0 },
    dispatch.session, dispatch.identity, bits, ticketResource, ticketRoot,
    enrollmentResource, enrollmentRoot, issueIngressBytes⟩

private def workflowChangedDispatch (dispatch : ApplicationDispatchCodec.Dispatch)
    (nextSnapshot : Int) (nextRequest : ApplicationDispatchCodec.Request) :
    ApplicationDispatchCodec.Dispatch :=
  let nextApp := { dispatch.app with snapshotVersion := nextSnapshot }
  { dispatch with app := nextApp, request := nextRequest }

/-- General regression: changing a request, current session-page root or app
checkpoint version leaves the cache key equal when the stable authority and
rights projection is equal. Each request still independently checks those
current roots in `checkCurrent`. -/
theorem sessionFingerprintKey_workflow_invariant (authorityRoot : Digest) (selection : Selection)
    (dispatch : ApplicationDispatchCodec.Dispatch) (bits : List Bool)
    (ticketResource : Nat) (ticketRoot : Digest)
    (enrollmentResource : Nat) (enrollmentRoot : Digest)
    (issueIngressBytes : List UInt8)
    (nextRoot : Digest) (nextSnapshot : Int)
    (nextRequest : ApplicationDispatchCodec.Request) :
    sessionFingerprintKey authorityRoot { selection with sessionRoot := nextRoot }
      (workflowChangedDispatch dispatch nextSnapshot nextRequest)
      bits ticketResource ticketRoot enrollmentResource enrollmentRoot issueIngressBytes =
    sessionFingerprintKey authorityRoot selection dispatch bits ticketResource ticketRoot
      enrollmentResource enrollmentRoot issueIngressBytes := by
  rfl

/-- These are exact source-preimage distinctions. Digest inequality additionally
relies on the deployed cSHAKE collision boundary, not a Lean axiom. -/
theorem sessionFingerprintKey_ticket_changes (authorityRoot : Digest) (selection : Selection)
    (dispatch : ApplicationDispatchCodec.Dispatch) (bits : List Bool)
    (ticketResource enrollmentResource : Nat) (ticketRoot nextTicketRoot enrollmentRoot : Digest)
    (issueIngressBytes : List UInt8) (changed : ticketRoot ≠ nextTicketRoot) :
    sessionFingerprintKey authorityRoot selection dispatch bits ticketResource ticketRoot
      enrollmentResource enrollmentRoot issueIngressBytes ≠
    sessionFingerprintKey authorityRoot selection dispatch bits ticketResource nextTicketRoot
      enrollmentResource enrollmentRoot issueIngressBytes := by
  intro equal
  exact changed (congrArg SessionFingerprintKey.ticketRoot equal)

theorem sessionFingerprintKey_enrollment_changes (authorityRoot : Digest) (selection : Selection)
    (dispatch : ApplicationDispatchCodec.Dispatch) (bits : List Bool)
    (ticketResource enrollmentResource : Nat) (ticketRoot enrollmentRoot nextEnrollmentRoot : Digest)
    (issueIngressBytes : List UInt8) (changed : enrollmentRoot ≠ nextEnrollmentRoot) :
    sessionFingerprintKey authorityRoot selection dispatch bits ticketResource ticketRoot
      enrollmentResource enrollmentRoot issueIngressBytes ≠
    sessionFingerprintKey authorityRoot selection dispatch bits ticketResource ticketRoot
      enrollmentResource nextEnrollmentRoot issueIngressBytes := by
  intro equal
  exact changed (congrArg SessionFingerprintKey.enrollmentRoot equal)

theorem sessionFingerprintKey_permissions_change (authorityRoot : Digest) (selection : Selection)
    (dispatch : ApplicationDispatchCodec.Dispatch) (bits nextBits : List Bool)
    (ticketResource enrollmentResource : Nat) (ticketRoot enrollmentRoot : Digest)
    (issueIngressBytes : List UInt8) (changed : bits ≠ nextBits) :
    sessionFingerprintKey authorityRoot selection dispatch bits ticketResource ticketRoot
      enrollmentResource enrollmentRoot issueIngressBytes ≠
    sessionFingerprintKey authorityRoot selection dispatch nextBits ticketResource ticketRoot
      enrollmentResource enrollmentRoot issueIngressBytes := by
  intro equal
  exact changed (congrArg SessionFingerprintKey.bits equal)

theorem sessionFingerprintKey_authority_changes (authorityRoot : Digest) (selection : Selection)
    (dispatch : ApplicationDispatchCodec.Dispatch) (bits : List Bool)
    (ticketResource enrollmentResource : Nat) (ticketRoot enrollmentRoot nextAuthority : Digest)
    (issueIngressBytes : List UInt8) (changed : authorityRoot ≠ nextAuthority) :
    sessionFingerprintKey authorityRoot selection dispatch bits ticketResource ticketRoot
      enrollmentResource enrollmentRoot issueIngressBytes ≠
    sessionFingerprintKey nextAuthority selection dispatch bits
      ticketResource ticketRoot enrollmentResource enrollmentRoot issueIngressBytes := by
  intro equal
  exact changed (congrArg SessionFingerprintKey.authorityRoot equal)

theorem sessionFingerprintKey_package_changes (authorityRoot : Digest) (selection : Selection)
    (dispatch : ApplicationDispatchCodec.Dispatch) (bits : List Bool)
    (ticketResource enrollmentResource : Nat) (ticketRoot enrollmentRoot nextPackage : Digest)
    (issueIngressBytes : List UInt8) (changed : dispatch.app.packageRoot ≠ nextPackage) :
    sessionFingerprintKey authorityRoot selection dispatch bits ticketResource ticketRoot
      enrollmentResource enrollmentRoot issueIngressBytes ≠
    sessionFingerprintKey authorityRoot selection
      { dispatch with app := { dispatch.app with packageRoot := nextPackage } }
      bits ticketResource ticketRoot enrollmentResource enrollmentRoot issueIngressBytes := by
  intro equal
  exact changed (congrArg (fun key : SessionFingerprintKey => key.app.packageRoot) equal)

/-- Versioned, unambiguous source preimage for the physical app-side session.
It intentionally does not encode the current session/app page root, request,
or snapshot checkpoint. -/
def sessionFingerprintStream : StreamCodec SessionFingerprintKey :=
  StreamCodec.xmap
    (StreamCodec.product digestStream
      (StreamCodec.product appStream
        (StreamCodec.product sessionStream
          (StreamCodec.product identityStream
            (StreamCodec.product (StreamCodec.list StreamCodec.bool)
              (StreamCodec.product StreamCodec.nat
                (StreamCodec.product digestStream
                  (StreamCodec.product StreamCodec.nat
                    (StreamCodec.product digestStream bytesStream)))))))))
    (fun key => (key.authorityRoot, key.app, key.session, key.identity, key.bits,
      key.ticketResource, key.ticketRoot, key.enrollmentResource,
      key.enrollmentRoot, key.issueIngressBytes))
    (fun (authorityRoot, app, session, identity, bits, ticketResource,
          ticketRoot, enrollmentResource, enrollmentRoot, issueIngressBytes) =>
      ⟨authorityRoot, app, session, identity, bits, ticketResource,
        ticketRoot, enrollmentResource, enrollmentRoot, issueIngressBytes⟩)
    (by intro key; cases key; rfl)

def sessionFingerprintMaterial (key : SessionFingerprintKey) : List UInt8 :=
  sessionFingerprintStream.encode key

/-- Ticket, enrollment, permission, authority and package changes above are
distinct *serialized preimages*. The final digest distinction is conditional
on the deployed hash collision boundary. -/
theorem sessionFingerprintMaterial_injective :
    Function.Injective sessionFingerprintMaterial :=
  lawful_encode_injective sessionFingerprintStream.toLawful

def sessionFingerprintOfKey (key : SessionFingerprintKey) : Digest :=
  (Sp800185Cshake256.hash
    "DREGG/APPLICATION/DISPATCH-SESSION-FINGERPRINT/v2".toUTF8.toList
    (sessionFingerprintMaterial key)).digest

theorem sessionFingerprint_workflow_invariant (authorityRoot : Digest) (selection : Selection)
    (dispatch : ApplicationDispatchCodec.Dispatch) (bits : List Bool)
    (ticketResource : Nat) (ticketRoot : Digest)
    (enrollmentResource : Nat) (enrollmentRoot : Digest)
    (issueIngressBytes : List UInt8)
    (nextRoot : Digest) (nextSnapshot : Int)
    (nextRequest : ApplicationDispatchCodec.Request) :
    sessionFingerprintOfKey (sessionFingerprintKey authorityRoot
      { selection with sessionRoot := nextRoot }
      (workflowChangedDispatch dispatch nextSnapshot nextRequest)
      bits ticketResource ticketRoot enrollmentResource enrollmentRoot issueIngressBytes) =
    sessionFingerprintOfKey (sessionFingerprintKey authorityRoot selection dispatch bits
      ticketResource ticketRoot enrollmentResource enrollmentRoot issueIngressBytes) := by
  rw [sessionFingerprintKey_workflow_invariant]

def sessionFingerprintKeyFor (authorityRoot : Digest) (selection : Selection)
    (ingress : ApplicationDispatchAdmissionIngress.Ingress)
    (bits : List Bool) (ticketResource : Nat) : SessionFingerprintKey :=
  sessionFingerprintKey authorityRoot selection ingress.dispatch.dispatch bits ticketResource
    ingress.ticketRoot ingress.dispatch.enrollmentResource
    ingress.dispatch.enrollmentRoot ingress.issueIngressBytes

private def workflowChangedIngress (ingress : ApplicationDispatchAdmissionIngress.Ingress)
    (nextAppRoot : Digest) (nextSnapshot : Int)
    (nextRequest : ApplicationDispatchCodec.Request) :
    ApplicationDispatchAdmissionIngress.Ingress :=
  let nextDispatch := workflowChangedDispatch ingress.dispatch.dispatch
    nextSnapshot nextRequest
  let rootChanged := { ingress.dispatch with appRoot := nextAppRoot }
  let nextBase := { rootChanged with dispatch := nextDispatch }
  { ingress with dispatch := nextBase }

/-- The source-level carrier may have a different app page root, session page
root, checkpoint and HTTP request on the next admitted turn while retaining
the exact same WebSession authority projection. -/
theorem sessionFingerprint_ingress_workflow_invariant (authorityRoot : Digest) (selection : Selection)
    (ingress : ApplicationDispatchAdmissionIngress.Ingress)
    (bits : List Bool) (ticketResource : Nat)
    (nextAppRoot nextSessionRoot : Digest) (nextSnapshot : Int)
    (nextRequest : ApplicationDispatchCodec.Request) :
    sessionFingerprintOfKey (sessionFingerprintKeyFor authorityRoot
      { selection with sessionRoot := nextSessionRoot }
      (workflowChangedIngress ingress nextAppRoot nextSnapshot nextRequest)
      bits ticketResource) =
    sessionFingerprintOfKey (sessionFingerprintKeyFor authorityRoot selection ingress bits ticketResource) := by
  rfl

/-- This is a cache invalidation key, never an external delivery permit. -/
def CheckedCurrentForSourceBytes.sessionFingerprint {F : Type} [Field F] [DecidableEq F]
    {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : Ambient} {ground : Ground deployment}
    {ingress : ApplicationDispatchAdmissionIngress.Ingress}
    {spec : Spec} {originalSourceBytes : List UInt8}
    (checked : CheckedCurrentForSourceBytes deployment profile ambient ground ingress spec originalSourceBytes) : Digest :=
  sessionFingerprintOfKey (sessionFingerprintKeyFor
    ground.authority.cell.root checked.selection ingress
    checked.bits spec.ticket.resource)

def CheckedCurrent.sessionFingerprint {F : Type} [Field F] [DecidableEq F]
    {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : Ambient} {ground : Ground deployment}
    {ingress : ApplicationDispatchAdmissionIngress.Ingress}
    {spec : Spec} {descriptor : ResourceBirth.Descriptor CanonicalCellRegistry.registry}
    (checked : CheckedCurrent deployment profile ambient ground ingress spec descriptor) : Digest :=
  sessionFingerprintOfKey (sessionFingerprintKeyFor
    ground.authority.cell.root checked.selection ingress
    checked.bits spec.ticket.resource)

/-- Check one loaded image from actual native signature/capability/policy and
old-page admission. This is intentionally not the final dispatch receiver:
the `spec`/`descriptor` must be obtained from a separately verified, admitted
historical issue at a prefix of this exact image before a pending event can be
committed. -/
def checkCurrentFromSourceBytes {F : Type} [Field F] [DecidableEq F]
    (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (native : CredentialSignatureIO.NativeConfig)
    (ground : Ground deployment) (ingress : ApplicationDispatchAdmissionIngress.Ingress)
    (spec : Spec) (originalSourceBytes : List UInt8) :
    IO (Except String (CheckedCurrentForSourceBytes deployment profile ambient ground ingress
      spec originalSourceBytes)) := do
  if profileExact : ingress.dispatch.domain = deployment.domain ∧
      ingress.dispatch.semantics = profile.semantics then
    if identityExact : identityMatches ingress = true then
      match selectedCommand : selectCommand ingress with
      | none => return .error "dispatch session observation selector missing"
      | some selection =>
          match decodedCommand : DeclaredResourceController.commandCodec.decode
              ingress.dispatch.signed.commandBytes with
          | none => return .error "noncanonical signed dispatch command"
          | some signedCommand =>
              if commandExact : matchesCommand ingress.dispatch selection ingress.parent
                  signedCommand = true then
                let expected := command ingress.dispatch selection ingress.parent
                match ← DeclaredResourceController.prepareAuthenticated deployment profile
                    ambient native ground expected ingress.dispatch.signed.authorityEnvelope with
                | .error _ => return .error "current dispatch session or agent preparation refused"
                | .ok prepared =>
                    if shape : DeclaredResourceController.PhysicalShape prepared then
                      if linked : linkedCurrentPolicies deployment profile ambient ground
                          ingress spec selection prepared = true then
                        let .ok appRead ← checkRead deployment profile ambient native ground
                          ingress selection prepared ingress.dispatch.dispatch.app.resource
                          ingress.dispatch.appObserveCapability ingress.dispatch.appRoot
                          ingress.dispatch.appObservationEnvelope
                          | return .error "current serving app observation refused"
                        let .ok manifestRead ← checkRead deployment profile ambient native ground
                          ingress selection prepared ingress.dispatch.dispatch.app.packageManifest
                          ingress.dispatch.manifestObserveCapability
                          ingress.dispatch.dispatch.app.manifestRoot
                          ingress.dispatch.manifestObservationEnvelope
                          | return .error "current manifest observation refused"
                        let .ok enrollmentRead ← checkRead deployment profile ambient native ground
                          ingress selection prepared ingress.dispatch.enrollmentResource
                          ingress.dispatch.enrollmentObserveCapability ingress.dispatch.enrollmentRoot
                          ingress.dispatch.enrollmentObservationEnvelope
                          | return .error "current enrollment observation refused"
                        let .ok ticketRead ← checkRead deployment profile ambient native ground
                          ingress selection prepared spec.ticket.resource
                          ingress.ticketObserveCapability ingress.ticketRoot
                          ingress.ticketObservationEnvelope
                          | return .error "current share ticket observation refused"
                        match appExact : appState ingress.dispatch.dispatch.app.resource
                            appRead.selected.observed.before with
                        | none => return .error "serving app state missing"
                        | some actualApp =>
                          match manifestExact : installedManifest deployment.domain
                              ingress.dispatch.dispatch.app.packageManifest
                              ingress.dispatch.dispatch.app.resource
                              ingress.dispatch.dispatch.app.packageVersion
                              manifestRead.selected.observed.before with
                          | none => return .error "installed manifest missing"
                          | some manifest =>
                            match enrollmentExact : installedEnrollment deployment.domain
                                ingress.dispatch.enrollmentResource
                                ingress.dispatch.dispatch.session.resource
                                ingress.dispatch.dispatch.session.generation
                                enrollmentRead.selected.observed.before with
                            | none => return .error "current session enrollment missing"
                            | some enrollment =>
                              match ticketExact : installedTicket deployment.domain
                                  spec.ticket.resource ticketRead.selected.observed.before with
                              | none => return .error "current share ticket missing"
                              | some ticket =>
                                if ticketLive : ticket.liveAt ambient.height = true then
                                  match meaningExact : selectedMeaning ingress spec actualApp
                                      manifest enrollment ticket with
                                  | none => return .error "dispatch identity or permission ceiling refused"
                                  | some bits =>
                                    if requestShape : dispatchRequestSafe
                                        ingress.dispatch.dispatch = true then
                                      if issuerCurrent : issuerLineageCurrentFromSourceBytes deployment profile
                                          ambient ground ingress spec selection originalSourceBytes prepared = true then
                                        match ← DeclaredResourceController.admit native prepared
                                            ingress.dispatch.signed with
                                        | .error _ => return .error "current dispatch mutation authority refused"
                                        | .ok invocation =>
                                          return .ok ⟨profileExact, identityExact, selection,
                                            selectedCommand, signedCommand, decodedCommand,
                                            commandExact, prepared, shape, linked, appRead,
                                            manifestRead, enrollmentRead, ticketRead, actualApp,
                                            appExact, manifest, manifestExact, enrollment,
                                            enrollmentExact, ticket, ticketExact, ticketLive, bits,
                                            meaningExact, requestShape, issuerCurrent, invocation⟩
                                      else return .error "current issuer delegation lineage refused"
                                    else return .error "unsupported or unsafe HTTP request shape"
                                else return .error "share ticket expired"
                      else return .error "current app/session/ticket policy linkage refused"
                    else return .error "dispatch physical mutation shape refused"
              else return .error "signed dispatch command differs from selected session/agent"
    else return .error "app-visible principal or app generation mismatch"
  else return .error "dispatch domain or semantics differs from deployment"


/-- Ordinary descriptor callers use the same checker and all the same current
signature, policy, role, resource and physical guards as before. -/
def checkCurrent {F : Type} [Field F] [DecidableEq F]
    (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (native : CredentialSignatureIO.NativeConfig)
    (ground : Ground deployment) (ingress : ApplicationDispatchAdmissionIngress.Ingress)
    (spec : Spec) (descriptor : ResourceBirth.Descriptor CanonicalCellRegistry.registry) :
    IO (Except String (CheckedCurrent deployment profile ambient ground ingress spec descriptor)) :=
  checkCurrentFromSourceBytes deployment profile ambient native ground ingress spec
    (ApplicationShareIssueSource.sourceBytes spec descriptor)


end Minidregg.Kernel.ApplicationDispatchAdmission
