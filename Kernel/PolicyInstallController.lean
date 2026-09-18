/-
# Kernel.PolicyInstallController -- checked source installation in complete authority domains

The controller decodes a canonical declaration, computes the routed successor authority state,
and derives a policy context from that candidate. Installation is authorized
against the original authority snapshot and original policy source. The new
source becomes selectable only from the returned canonical post-state.

This module returns an accepted effect and its exact post pages. A physical
handler must stage the immutable source blob and atomically install the changed shards
with the remaining hyperedge participants before publishing the result.
-/
import Compiler.CredentialAuthorityPolicyRegistry
import Compiler.DeclaredHyperedgeArtifact
import Compiler.CanonicalRuntimeProfile
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

abbrev RuntimeProfile := CanonicalRuntimeProfile.Profile

variable {F : Type} [Field F]

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

def declarationFrame : List UInt8 := "LOOM/POLICY/INSTALL".toUTF8.toList ++ [2]

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
  (Sp800185Cshake256.hash "LOOM.POLICY.INSTALL.ARGS/v2".toUTF8.toList
    (encodeDeclaration declaration)).digest

def effectDigest (declaration : Declaration) : Digest :=
  (Sp800185Cshake256.hash "LOOM.POLICY.INSTALL.EFFECT/v2".toUTF8.toList
    (encodeDeclaration declaration)).digest

/-- The selected head is read directly from the complete canonical schema;
absence is not the default epoch or an asserted host-side registry entry. -/
abbrev currentHead := CredentialAuthorityDomain.headAt

def newEntry (declaration : Declaration) : Entry :=
  .policy declaration.source.policyId declaration.source.version
    (policyRecordDigest declaration.source)

/-- All operation-dependent request coordinates are derived from this exact
declaration and actual complete authority state. `cost` is the declared source-byte budget;
monetary fees remain the conserved resource leg of the enclosing hyperedge. -/
def request (profile : RuntimeProfile F) (snapshot : Snapshot) (context : RequestContext)
    (declaration : Declaration) : Request .program where
  domain := snapshot.domain
  semantics := profile.semantics
  federation := context.federation
  subject := context.subject
  subjectKeyEpoch := context.subjectKeyEpoch
  target := ⟨declaration.source.policyId.value⟩
  verb := .installPolicy
  argsDigest := argsDigest declaration
  effectsDigest := effectDigest declaration
  nonce := declaration.nonce
  height := context.height
  preStateRoot := snapshot.cell.root
  policyId := declaration.source.policyId
  policyEpoch := context.policyEpoch
  cost := (encodeDeclaration declaration).length

def requestDigest (profile : RuntimeProfile F) (snapshot : Snapshot) (context : RequestContext)
    (declaration : Declaration) : Digest :=
  let wire := AuthorizationDeclaration.encodeRequest ⟨.program, request profile snapshot context declaration⟩
  (Sp800185Cshake256.hash "LOOM.POLICY.INSTALL.REQUEST/v2".toUTF8.toList
    ((StreamCodec.list StreamCodec.nat).encode
      (DeclaredHyperedgeArtifact.requestWords wire))).digest


def edits (profile : RuntimeProfile F) (snapshot : Snapshot) (context : RequestContext)
    (declaration : Declaration) :
    List CredentialAuthorityDomain.Edit :=
  CredentialAuthorityDomain.policyAndNullifierEdits snapshot declaration.source.policyId
    declaration.source.version (policyRecordDigest declaration.source)
    (requestDigest profile snapshot context declaration).value

inductive Reject where
  | malformedDeclaration
  | staleRoot
  | staleHead
  | wrongDomain
  | wrongSemantics
  | unsupportedPolicy
  | invalidSuccessor
  | pageUpdateRejected
  | subjectKeyEpoch
  | signature
  | policyEpoch
  | policyUnavailable
  | policyRejected
  | capability
  | nativeSignature (reason : CredentialSignatureAdmission.Reject)
  deriving DecidableEq, Repr

/-- Semantic source checks are retained beside the actual routed mutation. -/
structure Ready (profile : RuntimeProfile F) (snapshot : Snapshot) (declaration : Declaration) : Prop where
  rootExact : declaration.expectedPreRoot = snapshot.cell.root
  headExact : snapshot.currentHead declaration.source.policyId = declaration.expected
  domainExact : declaration.source.domain = snapshot.domain
  semanticsExact : declaration.source.semantics = profile.semantics
  supported : Minidregg.Compiler.supported profile.compilerProfile.compiler declaration.source.predicate = true
  successor : Successor declaration.expected declaration.source.source

structure CheckedPreparation (profile : RuntimeProfile F) (snapshot : Snapshot)
    (context : RequestContext) (declaration : Declaration) where
  ready : Ready profile snapshot declaration
  update : CredentialAuthorityDomain.PreparedPolicyAndNullifier snapshot
    declaration.source.policyId declaration.source.version (policyRecordDigest declaration.source)
    (requestDigest profile snapshot context declaration).value

/-- The source-owned domain editor derives the patch from the old selected
entry, checks routed pages, and proves their exact canonical-state projection.
The requester supplies neither the successor pages nor the field writes. -/
def prepareChecked (profile : RuntimeProfile F) (snapshot : Snapshot) (context : RequestContext)
    (declaration : Declaration) :
    Except Reject (CheckedPreparation profile snapshot context declaration) :=
  if rootExact : declaration.expectedPreRoot = snapshot.cell.root then
    if headExact : snapshot.currentHead declaration.source.policyId = declaration.expected then
      if domainExact : declaration.source.domain = snapshot.domain then
        if semanticsExact : declaration.source.semantics = profile.semantics then
          if supported : Minidregg.Compiler.supported profile.compilerProfile.compiler declaration.source.predicate = true then
            if successor : checkSuccessor declaration.expected declaration.source.source = true then
              match CredentialAuthorityDomain.preparePolicyAndNullifier snapshot declaration.source.policyId
                  declaration.source.version (policyRecordDigest declaration.source)
                  (requestDigest profile snapshot context declaration).value with
              | none => .error .pageUpdateRejected
              | some update => .ok
                  { ready := ⟨rootExact, headExact, domainExact, semanticsExact, supported,
                      (checkSuccessor_iff _ _).mp successor⟩
                    update := update }
            else .error .invalidSuccessor
          else .error .unsupportedPolicy
        else .error .wrongSemantics
      else .error .wrongDomain
    else .error .staleHead
  else .error .staleRoot

/-- An injectively named sequence of address bytes, with no field reduction.
The predicate compiler still performs its explicit cast-injectivity check. -/
def addressSlots : Nat → List UInt8 → List (String × Int)
  | _, [] => []
  | offset, byte :: bytes =>
      (s!"policy/address/{offset}", Int.ofNat byte.toNat) :: addressSlots (offset + 1) bytes

/-- The source-owned install view keeps absent policy fields absent. Request
identity is fixed by the declaration; projected slots cannot replace its
complete source/effect commitment. -/
def project (wanted : Request .program) (declaration : Declaration)
    (logical : LogicalState CredentialAuthorityState.schema.{0, 0}) :
    Minidregg.Pred.State :=
  let header := CanonicalRuntimeProfile.requestSlots wanted
  let fields := currentHead logical declaration.source.policyId
  { slots := header ++
      match fields with
      | none => []
      | some head =>
          ("policy/version", Int.ofNat head.version) ::
            addressSlots 0 (Sp800185Cshake256.digestCodec.encode head.address) }

def patch (profile : RuntimeProfile F) (snapshot : Snapshot) (context : RequestContext)
    (declaration : Declaration) :
    Patch CredentialAuthorityState.schema.{0, 0} Digest :=
  CredentialAuthorityDomain.editPatch snapshot (edits profile snapshot context declaration)

private def unitCodec : LawfulCodec Unit where
  encode := fun _ => []
  decode := fun bytes => if bytes = [] then some () else none
  decode_encode := by intro value; cases value; simp

/-- The family captures actual canonical pre-state and the entire derived
request. Its postcondition pins exactly the selected policy head; unrelated
authority fields may participate in the same composed turn. The fixed Pred
view below depends only on this head and the retained declaration/context. -/
def family (profile : RuntimeProfile F) (snapshot : Snapshot) (context : RequestContext) :
    SemanticEffectFamily CredentialAuthorityState.schema.{0, 0}
      CredentialAuthorityStateCodec.materializer Digest where
  pre := snapshot.cell
  request := fun declaration => ⟨.program, request profile snapshot context declaration⟩
  Declaration := Declaration
  declarationCodec := declarationCodec
  Outcome := fun _ => Unit
  outcomeCodec := fun _ => unitCodec
  ModeEvidence := fun declaration _ => CheckedPreparation profile snapshot context declaration
  Postcondition := fun declaration _ logical =>
    currentHead logical declaration.source.policyId =
      some ⟨declaration.source.version, policyRecordDigest declaration.source⟩ ∧
      logical.fields (.nullifier (requestDigest profile snapshot context declaration).value) = some true
  effectDigest := effectDigest
  patch := fun declaration _ => patch profile snapshot context declaration
  nullifier := fun declaration _ => some (requestDigest profile snapshot context declaration)
  Release := fun _ _ => Empty
  DeclassificationAuthority := fun _ _ => Empty
  ReleaseAuthorization := fun _ _ _ => Empty
  DisclosureAllowed := fun _ _ _ => True

structure Prepared (profile : RuntimeProfile F) (snapshot : Snapshot) (context : RequestContext) where
  declaration : Declaration
  candidate : Candidate (family profile snapshot context) snapshot.cell declaration ()

def Prepared.update {profile : RuntimeProfile F} {snapshot : Snapshot} {context : RequestContext}
    (prepared : Prepared profile snapshot context) :
    CredentialAuthorityDomain.Prepared snapshot (edits profile snapshot context prepared.declaration) :=
  prepared.candidate.modeEvidence.update.prepared

def Prepared.postPages {profile : RuntimeProfile F} {snapshot : Snapshot} {context : RequestContext}
    (prepared : Prepared profile snapshot context) : List Page := prepared.update.postPages

def prepare (profile : RuntimeProfile F) (snapshot : Snapshot) (context : RequestContext) (bytes : List UInt8) :
    Except Reject (Prepared profile snapshot context) :=
  match decodeDeclaration bytes with
  | none => .error .malformedDeclaration
  | some declaration => do
      let checked ← prepareChecked profile snapshot context declaration
      .ok
        { declaration := declaration
          candidate :=
            { preStateBound := rfl
              modeEvidence := checked
              validated := checked.update.prepared.validated
              postcondition := by
                change (currentHead checked.update.prepared.validated.apply.logical
                  declaration.source.policyId =
                    some ⟨declaration.source.version, policyRecordDigest declaration.source⟩) ∧
                  checked.update.prepared.validated.apply.logical.fields
                    (.nullifier (requestDigest profile snapshot context declaration).value) = some true
                rw [← checked.update.prepared.projectionExact]
                exact ⟨checked.update.head_exact, checked.update.nullifier_consumed⟩ } }

def Prepared.step {profile : RuntimeProfile F} {snapshot : Snapshot} {context : RequestContext}
    (prepared : Prepared profile snapshot context) : PolicyStepContext :=
  PolicyStepContext.ofCandidate
    (project (request profile snapshot context prepared.declaration) prepared.declaration)
    profile.semantics prepared.candidate

/-- Policy replacement has no signature-only or opaque-proof evidence mode.
Its native signature authenticates use of an actual stored control capability. -/
abbrev controlPortal := CredentialAuthorityPolicyRegistry.sourceCapabilityPortal

def Prepared.policyConfig [DecidableEq F]
    {profile : RuntimeProfile F} {snapshot : Snapshot} {context : RequestContext}
    (prepared : Prepared profile snapshot context) (store : PayloadStore) :
    CanonicalPolicyConfig F :=
  CredentialAuthorityPolicyRegistry.config profile.compilerProfile snapshot store
    (controlPortal snapshot (requestDigest profile snapshot context prepared.declaration).value) prepared.step

abbrev Prepared.Accepted [DecidableEq F]
    {profile : RuntimeProfile F} {snapshot : Snapshot} {context : RequestContext}
    (prepared : Prepared profile snapshot context) (store : PayloadStore) :=
  AcceptedCellEffect
    (portal := (prepared.policyConfig (F := F) store).portal)
    (authState := snapshot.authState)
    (family profile snapshot context) (request profile snapshot context prepared.declaration)
    snapshot.cell prepared.declaration ()

/-- The old stored policy-control capability is mandatory. A valid signature alone
is never authority to replace a resource's law. The native receipt binds use of
that capability to this exact source-derived request and operation marker. -/
def Prepared.admit [DecidableEq F]
    {profile : RuntimeProfile F} {snapshot : Snapshot} {context : RequestContext}
    (prepared : Prepared profile snapshot context) (store : PayloadStore)
    (controlCapability : CapabilityId)
    (receipt : CredentialSignatureAdmission.CheckedSignature snapshot) :
    Except Reject (prepared.Accepted store) :=
  let wanted := request profile snapshot context prepared.declaration
  let auth := snapshot.authState
  let config := prepared.policyConfig store
  match sourceCapabilityOnlyEvidence profile.compilerProfile snapshot store
      (requestDigest profile snapshot context prepared.declaration).value prepared.step
      wanted controlCapability receipt with
  | none => .error .capability
  | some evidence =>
      if epoch : wanted.policyEpoch = auth.policyEpoch wanted.policyId then
        match config.registry.resolve wanted.policyId wanted.policyEpoch with
        | none => .error .policyUnavailable
        | some committed =>
            let witness := canonicalWitness profile.compilerProfile.compiler committed
              prepared.step.oldState prepared.step.newState
            match CanonicalPolicyAdmission.admit config auth wanted evidence witness
                (.policy wanted.policyId wanted.policyEpoch) epoch with
            | none => .error .policyRejected
            | some authorization =>
                .ok (prepared.candidate.accept authorization rfl rfl rfl .sealed trivial)
      else .error .policyEpoch

/-- The only native signature producer is invoked on the wanted request computed
above. Its receipt is then checked by the same capability and compiled-policy path. -/
def Prepared.admitNative [DecidableEq F]
    {profile : RuntimeProfile F} {snapshot : Snapshot} {context : RequestContext}
    (prepared : Prepared profile snapshot context) (store : PayloadStore)
    (native : CredentialSignatureIO.NativeConfig) (controlCapability : CapabilityId)
    (envelopeBytes : List UInt8) : IO (Except Reject (prepared.Accepted store)) := do
  match ← CredentialSignatureAdmission.verifyNative native snapshot
      (requestDigest profile snapshot context prepared.declaration).value
      (request profile snapshot context prepared.declaration) envelopeBytes with
  | .error reason => return .error (.nativeSignature reason)
  | .ok receipt => return prepared.admit store controlCapability receipt

structure Installed [DecidableEq F]
    (profile : RuntimeProfile F) (snapshot : Snapshot) (context : RequestContext)
    (store : PayloadStore) where
  prepared : Prepared profile snapshot context
  accepted : prepared.Accepted store

def run [DecidableEq F]
    (profile : RuntimeProfile F) (snapshot : Snapshot) (context : RequestContext)
    (store : PayloadStore) (declarationBytes : List UInt8)
    (controlCapability : CapabilityId)
    (receipt : CredentialSignatureAdmission.CheckedSignature snapshot) :
    Except Reject (Installed profile snapshot context store) := do
  let prepared ← prepare profile snapshot context declarationBytes
  let accepted ← prepared.admit store controlCapability receipt
  .ok ⟨prepared, accepted⟩

def Installed.post [DecidableEq F]
    {profile : RuntimeProfile F} {snapshot : Snapshot} {context : RequestContext} {store : PayloadStore}
    (installed : Installed profile snapshot context store) : Materialized CredentialAuthorityStateCodec.materializer :=
  installed.accepted.prepared.post

def Installed.sourceBytes [DecidableEq F]
    {profile : RuntimeProfile F} {snapshot : Snapshot} {context : RequestContext} {store : PayloadStore}
    (installed : Installed profile snapshot context store) : List UInt8 :=
  policyRecordCodec.encode installed.prepared.declaration.source

theorem Installed.full_request_bound [DecidableEq F]
    {profile : RuntimeProfile F} {snapshot : Snapshot} {context : RequestContext} {store : PayloadStore}
    (installed : Installed profile snapshot context store) :
    (⟨ResourceKind.program, request profile snapshot context installed.prepared.declaration⟩ : Sigma Request) =
      (family profile snapshot context).request installed.prepared.declaration :=
  installed.accepted.requestBound

theorem Installed.actual_pre_bound [DecidableEq F]
    {profile : RuntimeProfile F} {snapshot : Snapshot} {context : RequestContext} {store : PayloadStore}
    (installed : Installed profile snapshot context store) :
    snapshot.cell = (family profile snapshot context).pre :=
  installed.accepted.preStateBound

/-- This is a property of every accepted installer token, including callers
outside `run`: the concrete receiving portal has no signature/proof bypass. -/
theorem Installed.control_capability_required [DecidableEq F]
    {profile : RuntimeProfile F} {snapshot : Snapshot} {context : RequestContext} {store : PayloadStore}
    (installed : Installed profile snapshot context store) :
    ∃ capability commitment,
      installed.accepted.authorization.evidence.capabilityValue = some (capability, commitment) ∧
      Verb.installPolicy ∈ capability.scope.verbs := by
  cases evidence : installed.accepted.authorization.evidence with
  | signature witness epoch verified => exact witness.elim
  | proof witness verified => exact witness.elim
  | capability cap commitment commitmentWitness membershipWitness issuerWitness
      selfRevocationWitness useWitness semantic useVerified commitmentVerified
      membershipVerified issuerVerified selfVerified ancestorVerified channelVerified =>
      exact ⟨cap, commitment, rfl, semantic.scope.verb⟩

/-- The source being changed selects its own current governing policy. A
caller cannot name an unrelated permissive policy in the request context. -/
theorem request_policy_is_target (profile : RuntimeProfile F) (snapshot : Snapshot) (context : RequestContext)
    (declaration : Declaration) :
    (request profile snapshot context declaration).policyId = declaration.source.policyId := rfl

/-- Every accepted installation satisfies the policy selected from the OLD
snapshot, evaluated on the exact canonical pre-state and installed post-state.
This holds for every accepted token, not only for calls through `run`. -/
theorem Installed.old_policy_evaluated [DecidableEq F]
    {profile : RuntimeProfile F} {snapshot : Snapshot} {context : RequestContext} {store : PayloadStore}
    (installed : Installed profile snapshot context store) :
    ∃ committed,
      (policyRegistry snapshot store).resolve installed.prepared.declaration.source.policyId
        context.policyEpoch = some committed ∧
      Minidregg.Pred.eval committed.record.predicate
        (project (request profile snapshot context installed.prepared.declaration) installed.prepared.declaration snapshot.cell.logical)
        (project (request profile snapshot context installed.prepared.declaration) installed.prepared.declaration installed.post.logical) = true := by
  have verified : (installed.prepared.policyConfig (F := F) store).verifies
      (request profile snapshot context installed.prepared.declaration)
      installed.accepted.authorization.policyWitness = true := by
    have accepted := installed.accepted.authorization.policyVerified
    exact (Bool.and_eq_true_iff.mp accepted).2
  exact (canonical_context_verifies_sound installed.prepared.step rfl verified).2.2.2

/-- The accepted post is the exact canonical projection of the routed shard
updates. This is the semantic side of the physical domain refinement. -/
theorem Installed.post_pages_exact [DecidableEq F]
    {profile : RuntimeProfile F} {snapshot : Snapshot} {context : RequestContext} {store : PayloadStore}
    (installed : Installed profile snapshot context store) :
    installed.post.logical =
      CredentialAuthorityDomain.logicalOfPages installed.prepared.postPages :=
  installed.prepared.update.projectionExact.symm

theorem Installed.source_selected_in_post [DecidableEq F]
    {profile : RuntimeProfile F} {snapshot : Snapshot} {context : RequestContext} {store : PayloadStore}
    (installed : Installed profile snapshot context store) :
    currentHead installed.post.logical installed.prepared.declaration.source.policyId =
      some ⟨installed.prepared.declaration.source.version,
        policyRecordDigest installed.prepared.declaration.source⟩ :=
  installed.accepted.postcondition.1

/-- A signature marker is consumed by the same routed authority patch as the
policy head. No standalone signature cache is treated as a durable replay guard. -/
theorem Installed.nullifier_consumed [DecidableEq F]
    {profile : RuntimeProfile F} {snapshot : Snapshot} {context : RequestContext} {store : PayloadStore}
    (installed : Installed profile snapshot context store) :
    installed.post.logical.fields
      (.nullifier (requestDigest profile snapshot context installed.prepared.declaration).value) =
      some true := installed.accepted.postcondition.2

theorem Installed.nullifier_was_fresh [DecidableEq F]
    {profile : RuntimeProfile F} {snapshot : Snapshot} {context : RequestContext} {store : PayloadStore}
    (installed : Installed profile snapshot context store) :
    CredentialAuthorityState.isNullified snapshot.cell
      (requestDigest profile snapshot context installed.prepared.declaration).value = false :=
  installed.accepted.modeEvidence.update.nullifierFresh

/-- The mandatory family postcondition transports the OLD selected predicate
to the actual joint post-state. It preserves the complete fixed policy view
without freezing unrelated canonical authority fields. -/
theorem Installed.old_policy_evaluated_at_final [DecidableEq F]
    {profile : RuntimeProfile F} {snapshot : Snapshot} {context : RequestContext} {store : PayloadStore}
    (installed : Installed profile snapshot context store)
    (finalState : LogicalState CredentialAuthorityState.schema.{0, 0})
    (preserved : (family profile snapshot context).Postcondition installed.prepared.declaration
      () finalState) :
    ∃ committed,
      (policyRegistry snapshot store).resolve installed.prepared.declaration.source.policyId
        context.policyEpoch = some committed ∧
      Minidregg.Pred.eval committed.record.predicate
        (project (request profile snapshot context installed.prepared.declaration) installed.prepared.declaration snapshot.cell.logical)
        (project (request profile snapshot context installed.prepared.declaration) installed.prepared.declaration finalState) = true := by
  obtain ⟨committed, resolved, evaluated⟩ := installed.old_policy_evaluated
  have headExact : currentHead finalState installed.prepared.declaration.source.policyId =
      some ⟨installed.prepared.declaration.source.version,
        policyRecordDigest installed.prepared.declaration.source⟩ := preserved.1
  have viewExact : project (request profile snapshot context installed.prepared.declaration) installed.prepared.declaration finalState =
      project (request profile snapshot context installed.prepared.declaration) installed.prepared.declaration installed.post.logical := by
    unfold project
    rw [headExact, installed.source_selected_in_post]
  exact ⟨committed, resolved, by rw [viewExact]; exact evaluated⟩

/-- The predecessor and epoch are checked against the actual old head, not
only against fields asserted in the installation declaration. -/
theorem Installed.source_successor [DecidableEq F]
    {profile : RuntimeProfile F} {snapshot : Snapshot} {context : RequestContext} {store : PayloadStore}
    (installed : Installed profile snapshot context store) :
    Successor (snapshot.currentHead installed.prepared.declaration.source.policyId)
      installed.prepared.declaration.source.source := by
  have ready := installed.accepted.modeEvidence.ready
  rw [ready.headExact]
  exact ready.successor

/-- Updating a policy removes the retired version's address from the actual
canonical post. It cannot remain selectable behind a newer current head. -/
theorem Installed.retired_address_absent [DecidableEq F]
    {profile : RuntimeProfile F} {snapshot : Snapshot} {context : RequestContext} {store : PayloadStore}
    (installed : Installed profile snapshot context store)
    (old : Head)
    (current : snapshot.currentHead installed.prepared.declaration.source.policyId = some old) :
    installed.post.logical.fields
      (.policyAddress installed.prepared.declaration.source.policyId old.version) = none := by
  have successor := installed.source_successor
  rw [current] at successor
  have different : old.version ≠ installed.prepared.declaration.source.version := by
    have advanced := successor.1
    change installed.prepared.declaration.source.version = old.version + 1 at advanced
    intro same
    exact (Nat.ne_of_lt (Nat.lt_succ_self old.version)) (same.trans advanced)
  rw [installed.post_pages_exact]
  exact installed.prepared.candidate.modeEvidence.update.retired_address_absent old current different

/-- Installation admits only sources in the actual compiler's vocabulary;
serializability of an AST is not evidence that it can execute. -/
theorem Installed.source_supported [DecidableEq F]
    {profile : RuntimeProfile F} {snapshot : Snapshot} {context : RequestContext} {store : PayloadStore}
    (installed : Installed profile snapshot context store) :
    Minidregg.Compiler.supported profile.compilerProfile.compiler installed.prepared.declaration.source.predicate = true :=
  installed.accepted.modeEvidence.ready.supported

/-- info: 'Minidregg.Kernel.PolicyInstallController.Installed.old_policy_evaluated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Installed.old_policy_evaluated
/-- info: 'Minidregg.Kernel.PolicyInstallController.Installed.source_selected_in_post' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Installed.source_selected_in_post
/-- info: 'Minidregg.Kernel.PolicyInstallController.Installed.source_successor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Installed.source_successor
/-- info: 'Minidregg.Kernel.PolicyInstallController.Installed.old_policy_evaluated_at_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Installed.old_policy_evaluated_at_final

end Minidregg.Kernel.PolicyInstallController
