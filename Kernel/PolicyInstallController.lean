/-
# Kernel.PolicyInstallController -- checked source installation on authority pages

The controller decodes a canonical declaration, computes the successor page,
and derives a policy context from that candidate. Installation is authorized
against the original authority snapshot and original policy source. The new
source becomes selectable only from the returned post-page.

This module returns an accepted effect and its exact post bytes. A physical
handler must stage the immutable source blob and atomically install the page
with the remaining hyperedge participants before publishing the result.
-/
import Compiler.CredentialAuthorityPolicyRegistry
import Compiler.DeclaredHyperedgeArtifact
import Theory.PolicyInstall

namespace Minidregg.Kernel.PolicyInstallController

open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.CredentialAuthorityPageMaterializer
open Minidregg.Compiler.CredentialAuthorityPolicyRegistry
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.CanonicalPolicyRegistry
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.PolicyInstall
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

def semantics : Digest :=
  (Sp800185Cshake256.hash "LOOM.POLICY.INSTALL.SEMANTICS/v1".toUTF8.toList []).digest

structure Declaration where
  expectedPreRoot : Digest
  expected : Option Head
  nonce : Nat
  source : PolicyRecord
  deriving DecidableEq, Repr

structure RequestContext where
  federation : FederationId
  subject : SubjectId
  subjectKeyEpoch : Epoch
  height : Height
  policyEpoch : Epoch
  deriving DecidableEq, Repr

def headStream : StreamCodec Head :=
  StreamCodec.xmap (StreamCodec.product StreamCodec.nat digestStream)
    (fun head => (head.version, head.address))
    (fun pair => ⟨pair.1, pair.2⟩) (by intro head; cases head; rfl)

abbrev DeclarationTuple := Digest × Option Head × Nat × List UInt8

def declarationTupleStream : StreamCodec DeclarationTuple :=
  StreamCodec.product digestStream
    (StreamCodec.product (StreamCodec.option headStream)
      (StreamCodec.product StreamCodec.nat (StreamCodec.list StreamCodec.byte)))

def declarationTuple (declaration : Declaration) : DeclarationTuple :=
  (declaration.expectedPreRoot, declaration.expected, declaration.nonce,
    policyRecordCodec.encode declaration.source)

def declarationOfTuple (tuple : DeclarationTuple) : Option Declaration := do
  let source ← policyRecordCodec.decode tuple.2.2.2
  some ⟨tuple.1, tuple.2.1, tuple.2.2.1, source⟩

@[simp] theorem declarationOfTuple_tuple (declaration : Declaration) :
    declarationOfTuple (declarationTuple declaration) = some declaration := by
  cases declaration
  simp [declarationTuple, declarationOfTuple, policyRecordCodec.decode_encode]

def declarationFrame : List UInt8 := "LOOM/POLICY/INSTALL".toUTF8.toList ++ [1]

def encodeDeclaration (declaration : Declaration) : List UInt8 :=
  declarationFrame ++ declarationTupleStream.encode (declarationTuple declaration)

def decodeDeclarationRaw (bytes : List UInt8) : Option Declaration :=
  if bytes.take declarationFrame.length = declarationFrame then do
    let tuple ← declarationTupleStream.toLawful.decode (bytes.drop declarationFrame.length)
    declarationOfTuple tuple
  else none

@[simp] theorem decodeDeclarationRaw_encode (declaration : Declaration) :
    decodeDeclarationRaw (encodeDeclaration declaration) = some declaration := by
  have payload := declarationTupleStream.toLawful.decode_encode (declarationTuple declaration)
  change declarationTupleStream.toLawful.decode
    (declarationTupleStream.encode (declarationTuple declaration)) =
      some (declarationTuple declaration) at payload
  simp [decodeDeclarationRaw, encodeDeclaration, payload]

def decodeDeclaration (bytes : List UInt8) : Option Declaration := do
  let declaration ← decodeDeclarationRaw bytes
  if encodeDeclaration declaration = bytes then some declaration else none

@[simp] theorem decodeDeclaration_encode (declaration : Declaration) :
    decodeDeclaration (encodeDeclaration declaration) = some declaration := by
  simp [decodeDeclaration]

theorem decodeDeclaration_canonical {bytes : List UInt8} {declaration : Declaration}
    (decoded : decodeDeclaration bytes = some declaration) :
    encodeDeclaration declaration = bytes := by
  unfold decodeDeclaration at decoded
  cases raw : decodeDeclarationRaw bytes with
  | none => simp [raw] at decoded
  | some selected =>
      simp only [raw, bind, Option.bind] at decoded
      split at decoded
      next canonical =>
        cases Option.some.inj decoded
        exact canonical
      next => contradiction

def declarationCodec : LawfulCodec Declaration where
  encode := encodeDeclaration
  decode := decodeDeclaration
  decode_encode := decodeDeclaration_encode

def argsDigest (declaration : Declaration) : Digest :=
  (Sp800185Cshake256.hash "LOOM.POLICY.INSTALL.ARGS/v1".toUTF8.toList
    (encodeDeclaration declaration)).digest

def effectDigest (declaration : Declaration) : Digest :=
  (Sp800185Cshake256.hash "LOOM.POLICY.INSTALL.EFFECT/v1".toUTF8.toList
    (encodeDeclaration declaration)).digest

/-- The current head is found from the actual page, with absence preserved.
Validity of a `Snapshot` excludes multiple current heads for one policy id. -/
def currentHead (page : Page) (policyId : PolicyId) : Option Head :=
  page.entries.findSome? fun entry =>
    match entry with
    | .policy selected version address =>
        if selected = policyId then some ⟨version, address⟩ else none
    | _ => none

def newEntry (declaration : Declaration) : Entry :=
  .policy declaration.source.policyId declaration.source.version
    (policyRecordDigest declaration.source)

inductive Reject where
  | malformedDeclaration
  | staleRoot
  | staleHead
  | wrongDomain
  | wrongSemantics
  | unsupportedPolicy
  | invalidSuccessor
  | pageUpdateRejected
  | invalidPatch
  | subjectKeyEpoch
  | signature
  | policyEpoch
  | policyUnavailable
  | policyRejected
  deriving DecidableEq, Repr

/-- The semantic source checks retained by every prepared mutation. -/
structure Ready (snapshot : Snapshot) (declaration : Declaration) : Prop where
  rootExact : declaration.expectedPreRoot = snapshot.cell.root
  headExact : currentHead snapshot.page declaration.source.policyId = declaration.expected
  domainExact : declaration.source.domain = snapshot.page.authorityDomain
  semanticsExact : declaration.source.semantics = semantics
  supported : Minidregg.Compiler.supported declaration.source.predicate = true
  successor : Successor declaration.expected declaration.source.source

/-- All semantic checks precede the single page mutation. An update uses
exact entry replacement, never insertion that shadows an old policy head. -/
def prepareChecked (snapshot : Snapshot) (declaration : Declaration) :
    Except Reject { post : Page // post.Valid ∧ post.Contains (newEntry declaration) ∧
      Ready snapshot declaration } :=
  if rootExact : declaration.expectedPreRoot = snapshot.cell.root then
    if headExact : currentHead snapshot.page declaration.source.policyId = declaration.expected then
      if domainExact : declaration.source.domain = snapshot.page.authorityDomain then
        if semanticsExact : declaration.source.semantics = semantics then
          if supported : Minidregg.Compiler.supported declaration.source.predicate = true then
            if successor : checkSuccessor declaration.expected declaration.source.source = true then
              let ready : Ready snapshot declaration :=
                ⟨rootExact, headExact, domainExact, semanticsExact, supported,
                  (checkSuccessor_iff _ _).mp successor⟩
              match declaration.expected with
              | none =>
                  match inserted : snapshot.page.admitInsert (newEntry declaration) with
                  | .ok post => .ok ⟨post.val, post.property,
                      Page.insert_contains (Page.admitInsert_exact inserted).2.2, ready⟩
                  | .error _ => .error .pageUpdateRejected
              | some old =>
                  match replaced : snapshot.page.admitReplace
                      (.policy declaration.source.policyId old.version old.address)
                      (newEntry declaration) with
                  | .ok post => .ok ⟨post.val, post.property,
                      Page.replaceEntry_contains
                        (page := snapshot.page)
                        (old := .policy declaration.source.policyId old.version old.address)
                        (replacement := newEntry declaration) (post := post.val) (by
                        simp [Page.replaceEntry?, (Page.admitReplace_exact replaced).2.1,
                          (Page.admitReplace_exact replaced).2.2]), ready⟩
                  | .error _ => .error .pageUpdateRejected
            else .error .invalidSuccessor
          else .error .unsupportedPolicy
        else .error .wrongSemantics
      else .error .wrongDomain
    else .error .staleHead
  else .error .staleRoot

def preparePost (snapshot : Snapshot) (declaration : Declaration) : Except Reject Page :=
  (prepareChecked snapshot declaration).map Subtype.val

theorem preparePost_checked {snapshot : Snapshot} {declaration : Declaration}
    {post : Page} (accepted : preparePost snapshot declaration = .ok post) :
    post.Valid ∧ post.Contains (newEntry declaration) ∧ Ready snapshot declaration := by
  cases checked : prepareChecked snapshot declaration with
  | error reason => simp [preparePost, checked, Except.map] at accepted
  | ok result =>
      have same : result.val = post := by
        simpa [preparePost, checked, Except.map] using accepted
      rw [← same]
      exact result.property

theorem preparePost_valid_contains {snapshot : Snapshot} {declaration : Declaration}
    {post : Page} (accepted : preparePost snapshot declaration = .ok post) :
    post.Valid ∧ post.Contains (newEntry declaration) :=
  ⟨(preparePost_checked accepted).1, (preparePost_checked accepted).2.1⟩

/-- An injectively named sequence of address bytes, with no field reduction.
The predicate compiler still performs its explicit cast-injectivity check. -/
def addressSlots : Nat → List UInt8 → List (String × Int)
  | _, [] => []
  | offset, byte :: bytes =>
      (s!"policy/address/{offset}", Int.ofNat byte.toNat) :: addressSlots (offset + 1) bytes

/-- The source-owned install view keeps absent policy fields absent. Request
identity is fixed by the declaration; projected slots cannot replace its
complete source/effect commitment. -/
def project (context : RequestContext) (declaration : Declaration)
    (logical : LogicalState CredentialAuthorityPageMaterializer.schema) :
    Minidregg.Pred.State :=
  let header :=
    [ ("request/program", Int.ofNat declaration.source.policyId.value)
    , ("request/nonce", Int.ofNat declaration.nonce)
    , ("request/subject", Int.ofNat context.subject.value)
    , ("request/subjectKeyEpoch", Int.ofNat context.subjectKeyEpoch)
    , ("request/federation", Int.ofNat context.federation.value)
    , ("request/height", Int.ofNat context.height)
    , ("request/policyEpoch", Int.ofNat context.policyEpoch) ]
  let fields := do
    let page ← pageAt logical
    currentHead page declaration.source.policyId
  { slots := header ++
      match fields with
      | none => []
      | some head =>
          ("policy/version", Int.ofNat head.version) ::
            addressSlots 0 (Sp800185Cshake256.digestCodec.encode head.address) }

def patch (snapshot : Snapshot) (post : Page) :
    Patch CredentialAuthorityPageMaterializer.schema Digest where
  expectedPreRoot := snapshot.cell.root
  fieldFootprint := {()}
  resourceFootprint := ∅
  fieldWrites := [{ field := (), value := some post }]
  resourceWrites := []

/-- All operation-dependent request coordinates are derived from this exact
declaration and actual pre-page. `cost` is the declared source-byte budget;
monetary fees remain the conserved resource leg of the enclosing hyperedge. -/
def request (snapshot : Snapshot) (context : RequestContext)
    (declaration : Declaration) : Request .program where
  domain := snapshot.page.authorityDomain
  semantics := semantics
  federation := context.federation
  subject := context.subject
  subjectKeyEpoch := context.subjectKeyEpoch
  target := ⟨declaration.source.policyId.value⟩
  verb := .installProgram
  argsDigest := argsDigest declaration
  effectsDigest := effectDigest declaration
  nonce := declaration.nonce
  height := context.height
  preStateRoot := snapshot.cell.root
  policyId := declaration.source.policyId
  policyEpoch := context.policyEpoch
  cost := (encodeDeclaration declaration).length

def requestDigest (snapshot : Snapshot) (context : RequestContext)
    (declaration : Declaration) : Digest :=
  let wire := AuthorizationDeclaration.encodeRequest ⟨.program, request snapshot context declaration⟩
  (Sp800185Cshake256.hash "LOOM.POLICY.INSTALL.REQUEST/v1".toUTF8.toList
    ((StreamCodec.list StreamCodec.nat).encode
      (DeclaredHyperedgeArtifact.requestWords wire))).digest

/-- The existing common family captures both the actual canonical pre-state
and the entire derived request. Neither can be relabelled when minting an
accepted effect. The mode evidence is the result of the source-owned installer. -/
def family (snapshot : Snapshot) (context : RequestContext) :
    SemanticEffectFamily CredentialAuthorityPageMaterializer.schema materializer Digest where
  pre := snapshot.cell
  request := fun declaration => ⟨.program, request snapshot context declaration⟩
  Declaration := Declaration
  declarationCodec := declarationCodec
  Outcome := fun _ => Page
  outcomeCodec := fun _ => pageStream.toLawful
  ModeEvidence := fun declaration post => PLift (preparePost snapshot declaration = .ok post)
  effectDigest := effectDigest
  patch := fun _ post => patch snapshot post
  nullifier := fun declaration _ => some (requestDigest snapshot context declaration)
  Release := fun _ _ => Empty
  DeclassificationAuthority := fun _ _ => Empty
  ReleaseAuthorization := fun _ _ _ => Empty
  DisclosureAllowed := fun _ _ _ => True

structure Prepared (snapshot : Snapshot) (context : RequestContext) where
  declaration : Declaration
  outcome : Page
  candidate : Candidate (family snapshot context) snapshot.cell declaration outcome

def prepare (snapshot : Snapshot) (context : RequestContext) (bytes : List UInt8) :
    Except Reject (Prepared snapshot context) :=
  match decodeDeclaration bytes with
  | none => .error .malformedDeclaration
  | some declaration =>
      match checked : preparePost snapshot declaration with
      | .error reason => .error reason
      | .ok post =>
          match validate materializer snapshot.cell (patch snapshot post) with
          | .rejected _ => .error .invalidPatch
          | .accepted validated =>
              .ok
                { declaration := declaration
                  outcome := post
                  candidate :=
                    { preStateBound := rfl
                      modeEvidence := ⟨checked⟩
                      validated := validated } }

def Prepared.step {snapshot : Snapshot} {context : RequestContext}
    (prepared : Prepared snapshot context) : PolicyStepContext :=
  PolicyStepContext.ofCandidate (project context prepared.declaration) semantics prepared.candidate

def Prepared.policyConfig {F : Type} [Field F] [DecidableEq F]
    {snapshot : Snapshot} {context : RequestContext}
    (prepared : Prepared snapshot context) (store : PayloadStore) (base : Portal) :
    CanonicalPolicyConfig F :=
  CredentialAuthorityPolicyRegistry.config snapshot store base prepared.step

abbrev Prepared.Accepted {F : Type} [Field F] [DecidableEq F]
    {snapshot : Snapshot} {context : RequestContext}
    (prepared : Prepared snapshot context) (store : PayloadStore) (base : Portal) :=
  AcceptedCellEffect
    (portal := (prepared.policyConfig (F := F) store base).portal)
    (authState := CredentialAuthorityPolicyRegistry.projection.authState snapshot.cell)
    (family snapshot context) (request snapshot context prepared.declaration)
    snapshot.cell prepared.declaration prepared.outcome

/-- Evidence is checked here, rather than supplied as an asserted Lean proof.
Policy source is resolved from the OLD snapshot even when this operation is
replacing that same policy. The canonical compiler constructs its own witness. -/
def Prepared.admit {F : Type} [Field F] [DecidableEq F]
    {snapshot : Snapshot} {context : RequestContext}
    (prepared : Prepared snapshot context) (store : PayloadStore) (base : Portal)
    (signature : base.SignatureWitness) : Except Reject (prepared.Accepted (F := F) store base) :=
  let wanted := request snapshot context prepared.declaration
  let auth := CredentialAuthorityPolicyRegistry.projection.authState snapshot.cell
  let config := prepared.policyConfig (F := F) store base
  if keyEpoch : wanted.subjectKeyEpoch = auth.subjectKeyEpoch wanted.subject then
    if verified : base.verifySignature wanted signature = true then
      if epoch : wanted.policyEpoch = auth.policyEpoch wanted.policyId then
        match config.registry.resolve wanted.policyId wanted.policyEpoch with
        | none => .error .policyUnavailable
        | some committed =>
            let evidence : Evidence config.portal auth wanted :=
              .signature signature keyEpoch verified
            let witness := canonicalWitness committed prepared.step.oldState prepared.step.newState
            match CanonicalPolicyAdmission.admit config auth wanted evidence witness () epoch with
            | none => .error .policyRejected
            | some authorization =>
                .ok (prepared.candidate.accept authorization rfl rfl rfl .sealed trivial)
      else .error .policyEpoch
    else .error .signature
  else .error .subjectKeyEpoch

structure Installed {F : Type} [Field F] [DecidableEq F]
    (snapshot : Snapshot) (context : RequestContext) (store : PayloadStore) (base : Portal) where
  prepared : Prepared snapshot context
  accepted : prepared.Accepted (F := F) store base

def run {F : Type} [Field F] [DecidableEq F]
    (snapshot : Snapshot) (context : RequestContext) (store : PayloadStore) (base : Portal)
    (declarationBytes : List UInt8) (signature : base.SignatureWitness) :
    Except Reject (Installed (F := F) snapshot context store base) := do
  let prepared ← prepare snapshot context declarationBytes
  let accepted ← prepared.admit (F := F) store base signature
  .ok ⟨prepared, accepted⟩

def Installed.post {F : Type} [Field F] [DecidableEq F]
    {snapshot : Snapshot} {context : RequestContext} {store : PayloadStore} {base : Portal}
    (installed : Installed (F := F) snapshot context store base) : Materialized materializer :=
  installed.accepted.prepared.post

def Installed.sourceBytes {F : Type} [Field F] [DecidableEq F]
    {snapshot : Snapshot} {context : RequestContext} {store : PayloadStore} {base : Portal}
    (installed : Installed (F := F) snapshot context store base) : List UInt8 :=
  policyRecordCodec.encode installed.prepared.declaration.source

theorem Installed.full_request_bound {F : Type} [Field F] [DecidableEq F]
    {snapshot : Snapshot} {context : RequestContext} {store : PayloadStore} {base : Portal}
    (installed : Installed (F := F) snapshot context store base) :
    (⟨ResourceKind.program, request snapshot context installed.prepared.declaration⟩ : Sigma Request) =
      (family snapshot context).request installed.prepared.declaration :=
  installed.accepted.requestBound

theorem Installed.actual_pre_bound {F : Type} [Field F] [DecidableEq F]
    {snapshot : Snapshot} {context : RequestContext} {store : PayloadStore} {base : Portal}
    (installed : Installed (F := F) snapshot context store base) :
    snapshot.cell = (family snapshot context).pre :=
  installed.accepted.preStateBound

/-- The source being changed selects its own current governing policy. A
caller cannot name an unrelated permissive policy in the request context. -/
theorem request_policy_is_target (snapshot : Snapshot) (context : RequestContext)
    (declaration : Declaration) :
    (request snapshot context declaration).policyId = declaration.source.policyId := rfl

/-- Every accepted installation satisfies the policy selected from the OLD
snapshot, evaluated on the exact canonical pre-state and installed post-state.
This holds for every accepted token, not only for calls through `run`. -/
theorem Installed.old_policy_evaluated {F : Type} [Field F] [DecidableEq F]
    {snapshot : Snapshot} {context : RequestContext} {store : PayloadStore} {base : Portal}
    (installed : Installed (F := F) snapshot context store base) :
    ∃ committed,
      (policyRegistry snapshot store).resolve installed.prepared.declaration.source.policyId
        context.policyEpoch = some committed ∧
      Minidregg.Pred.eval committed.record.predicate
        (project context installed.prepared.declaration snapshot.cell.logical)
        (project context installed.prepared.declaration installed.post.logical) = true := by
  have verified : (installed.prepared.policyConfig (F := F) store base).verifies
      (request snapshot context installed.prepared.declaration)
      installed.accepted.authorization.policyWitness = true := by
    have accepted := installed.accepted.authorization.policyVerified
    exact (Bool.and_eq_true_iff.mp accepted).2
  exact (canonical_context_verifies_sound installed.prepared.step rfl verified).2.2.2

theorem Installed.post_page {F : Type} [Field F] [DecidableEq F]
    {snapshot : Snapshot} {context : RequestContext} {store : PayloadStore} {base : Portal}
    (installed : Installed (F := F) snapshot context store base) :
    pageAt installed.post.logical = some installed.prepared.outcome := by
  change (applyFieldWrites (patch snapshot installed.prepared.outcome).fieldWrites
    snapshot.cell.logical.fields) () = some installed.prepared.outcome
  simp [patch, applyFieldWrites, FieldStore.assign]
  rfl

/-- The installed page contains the complete checked source's actual content
address and version. The proof is extracted from the same mode evidence that
the accepted effect retains. -/
theorem Installed.source_selected_in_post {F : Type} [Field F] [DecidableEq F]
    {snapshot : Snapshot} {context : RequestContext} {store : PayloadStore} {base : Portal}
    (installed : Installed (F := F) snapshot context store base) :
    installed.prepared.outcome.Valid ∧
    installed.prepared.outcome.Contains (newEntry installed.prepared.declaration) :=
  preparePost_valid_contains installed.accepted.modeEvidence.down

/-- The predecessor and epoch are checked against the actual old head, not
only against fields asserted in the installation declaration. -/
theorem Installed.source_successor {F : Type} [Field F] [DecidableEq F]
    {snapshot : Snapshot} {context : RequestContext} {store : PayloadStore} {base : Portal}
    (installed : Installed (F := F) snapshot context store base) :
    Successor (currentHead snapshot.page installed.prepared.declaration.source.policyId)
      installed.prepared.declaration.source.source := by
  have ready := (preparePost_checked installed.accepted.modeEvidence.down).2.2
  rw [ready.headExact]
  exact ready.successor

/-- Installation admits only sources in the actual compiler's vocabulary;
serializability of an AST is not evidence that it can execute. -/
theorem Installed.source_supported {F : Type} [Field F] [DecidableEq F]
    {snapshot : Snapshot} {context : RequestContext} {store : PayloadStore} {base : Portal}
    (installed : Installed (F := F) snapshot context store base) :
    Minidregg.Compiler.supported installed.prepared.declaration.source.predicate = true :=
  (preparePost_checked installed.accepted.modeEvidence.down).2.2.supported

/-- info: 'Minidregg.Kernel.PolicyInstallController.Installed.old_policy_evaluated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Installed.old_policy_evaluated
/-- info: 'Minidregg.Kernel.PolicyInstallController.Installed.source_selected_in_post' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Installed.source_selected_in_post
/-- info: 'Minidregg.Kernel.PolicyInstallController.Installed.source_successor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Installed.source_successor

end Minidregg.Kernel.PolicyInstallController
