/-
# `Assurance/SealedHyperdocGrammarGate.lean` — Sealed `Hyperdocument` Blinded-Patch Gate with Attenuated Grammar Capabilities

Welds:
1. `Theory/GrammarTypedCapability.lean` (`GrammarPolicy`, `grammarPolicyAttenuates_sound`,
   `policyChainAttenuates_sound`, `GrammarCapLineage`),
2. `Theory/Hyperdocument.lean` & `Theory/HyperdocumentOperations.lean` (`AtomKind.sealedObject`,
   `EditAtomPayload`, `editAtomWrites`, `PrincipalRef`, `Capability` validity/epochs/revocation),
3. `Compiler/Tower256PrivateContentCert.lean` (`saltedContentCommit`, `saltedRoot_eq_or_collision`,
   `checkPrivate`, `checkPrivate_sound_or_collision`, `StepSamplingMiss`, `PrivateCertCollision`),
4. `Compiler/PolicyAstTransducerEmit.lean` (`absentW_iff_plain`, `absentW_iff_padded_complement`), and
5. `Assurance/CertificateComposition.lean` (shared-root conjunctive certificate discipline `L1`)

into the **Sealed `Hyperdocument` Blinded-Patch Gate (`verifySealedHyperdocPatch` &
`verifySealedHyperdocSuccinctGuards`)**:

- **`verifySealedHyperdocPatch_sound_or_collision`:**
  An accepted blinded patch to a sealed `Hyperdocument` atom cell guarantees that for **any**
  committed salted payload `(wNamed, sNamed)` matching `(stmt.patchLen, stmt.saltedPatchRoot)`:
  1. `(wNamed, wit.ruleSeq, stmt.claimedAst)` satisfies the **root authority's `GrammarPolicy`**
     (via transitive `policyChainAttenuates_sound` along the multi-hop delegation chain),
  2. all forbidden secret patterns in `stmt.rootPolicy.redactRules` are scrubbed (`AbsentPlain` and
     `MatchesRegex _ (Regex.paddedComplement _)`),
  3. every `AutomatonBound` guard of `stmt.rootPolicy` holds (`Dfaops.satisfiesClaim`),
  4. **Unique Authorized AST (`ast_root = ast_leaf = stmt.claimedAst`):** no duplicate-key or
     wider-rule parse in `stmt.rootPolicy` can synthesize any other AST,
  5. every capability hop in the chain is unrevoked, epoch-pinned, and writes a `.sealedObject`
     `Hyperdocument` atom with zero cleartext durable bytes (`payload = []`) —
  **OR** exhibits an explicit `StepSamplingMiss` (only in succinct sampled-step mode; `False` in
  direct blinded-opening mode) **OR** constructively extracts an explicit SP 800-185 `cSHAKE256`
  `FramedXofCollision cshakeC` (`SaltedCollision` / `PrivateCertCollision`)!

Import boundary: `Assurance/` tier (`Theory.*`, `Compiler.*`, `Selvage.*`, `Assurance.*`).
-/
import Theory.GrammarTypedCapability
import Theory.CredentialLineageAdmission
import Theory.Hyperdocument
import Theory.HyperdocumentOperations
import Compiler.Tower256PrivateContentCert
import Compiler.PolicyAstTransducerEmit
import Assurance.CertificateComposition

namespace Minidregg.Assurance.SealedHyperdocGrammarGate

open Minidregg.Theory
open Minidregg.Theory.VerifiedAstTransducer
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.CredentialAuthorityFamily
open Minidregg.Theory.CredentialLineageAdmission
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.HyperdocumentOperations
open Minidregg.Theory.GrammarTypedCapability
open Minidregg.Selvage
open Minidregg.Compiler.Tower256CshakeMerkleBinding (FramedXofCollision)
open Minidregg.Compiler.Tower256CoordinateMerkle (cshakeC)
open Minidregg.Compiler.Tower256ContentCert (ClaimData DfaTable automatonCommit)
open Minidregg.Compiler.Tower256AdditiveFriRawController (RawTranscript)
open Minidregg.Compiler.Tower256AdditiveFriSuccinctController (Consistent)
open Minidregg.Compiler.Tower256AdditiveFriRawDeployment (rawPcs)
open Minidregg.Compiler.Tower256PrivateContentCert
open Minidregg.Compiler.PolicyAstTransducerEmit

set_option autoImplicit false

/-! ## §1. Exact Isomorphism Between `Theory.DfaSpec` and `Compiler.DfaTable` + `ClaimData` -/

/-- Exact structural projection from `Theory.GrammarTypedCapability.DfaSpec` to
`Compiler.Tower256ContentCert.DfaTable`. -/
def dfaToTable (d : DfaSpec) : DfaTable where
  states    := d.states
  initial   := d.initial
  accepting := d.accepting
  delta     := d.delta

/-- Inverse projection from `DfaTable` to `DfaSpec`. -/
def dfaOfTable (t : DfaTable) : DfaSpec where
  states    := t.states
  initial   := t.initial
  accepting := t.accepting
  delta     := t.delta

theorem dfaSpec_wellFormed_toDfaTable {d : DfaSpec} (hd : d.WellFormed) :
    (dfaToTable d).WellFormed :=
  ⟨hd.2.1, hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2⟩

theorem dfaSpec_step_eq_table (d : DfaSpec) (s : Nat) (b : UInt8) :
    (dfaToTable d).step s b = d.step s b := rfl

theorem dfaSpec_run_eq_table (d : DfaSpec) (w : List UInt8) :
    (dfaToTable d).run w = d.run w := rfl

theorem dfaSpec_accepts_eq_table (d : DfaSpec) (w : List UInt8) :
    (dfaToTable d).accepts w = d.accepts w := rfl

theorem dfaSpec_runCount_eq_hitCount (d : DfaSpec) (w : List UInt8) :
    Dfaops.runCount (dfaToTable d) w = d.hitCount w := by
  unfold Dfaops.runCount DfaSpec.hitCount
  have haux : ∀ (s c : Nat) (u : List UInt8),
      Dfaops.runStateCountFrom (dfaToTable d) s c u = d.runStateCountFrom s c u := by
    intro s c u
    induction u generalizing s c with
    | nil => rfl
    | cons b rest ih =>
        simp only [Dfaops.runStateCountFrom, DfaSpec.runStateCountFrom]
        exact ih _ _
  exact congrArg Prod.snd (haux d.initial 0 w)

/-- Canonical `ClaimData` encoding of each `AutomatonBound` mode. -/
def boundToClaim : AutomatonBound → ClaimData
  | .mustAccept _ => .accept true
  | .mustReject _ => .accept false
  | .maxHits _ hi => .bound 0 hi
  | .exactHits _ n => .count n
  | .rangeHits _ lo hi => .bound lo hi

/-- Exact agreement between `Dfaops.satisfiesClaim` and `AutomatonBound.holds` across all 5 modes. -/
theorem satisfiesClaim_boundToClaim_eq (b : AutomatonBound) (w : List UInt8) :
    Dfaops.satisfiesClaim (dfaToTable b.dfa) (boundToClaim b) w = b.holds w := by
  cases b with
  | mustAccept d =>
      simp only [boundToClaim, AutomatonBound.dfa, AutomatonBound.holds,
        Dfaops.satisfiesClaim, Dfaops.claimDecide, dfaSpec_accepts_eq_table, beq_true]
  | mustReject d =>
      simp only [boundToClaim, AutomatonBound.dfa, AutomatonBound.holds,
        Dfaops.satisfiesClaim, Dfaops.claimDecide, dfaSpec_accepts_eq_table]
      cases d.accepts w <;> rfl
  | maxHits d hi =>
      simp only [boundToClaim, AutomatonBound.dfa, AutomatonBound.holds,
        Dfaops.satisfiesClaim, Dfaops.claimDecide, dfaSpec_runCount_eq_hitCount,
        Nat.zero_le, decide_true, Bool.true_and]
  | exactHits d n =>
      simp only [boundToClaim, AutomatonBound.dfa, AutomatonBound.holds,
        Dfaops.satisfiesClaim, Dfaops.claimDecide, dfaSpec_runCount_eq_hitCount, beq_eq_decide]
  | rangeHits d lo hi =>
      simp only [boundToClaim, AutomatonBound.dfa, AutomatonBound.holds,
        Dfaops.satisfiesClaim, Dfaops.claimDecide, dfaSpec_runCount_eq_hitCount]

/-! ## §2. Epoch-Pinned, Non-Revoked Capability Chain & Sealed `Hyperdocument` Patch Gate -/

/-- One hop in an attenuated capability chain presented to the sealed `Hyperdocument` gate. -/
structure DelegatedGrammarHop (NT : Type) {SemOp Val : Type} (sem : AttrSemantics SemOp Val) where
  capability : Capability .object
  policy     : GrammarPolicy NT sem

/-- Public statement for a blinded patch to a sealed `Hyperdocument` atom cell. -/
structure SealedHyperdocPatchStmt (NT : Type) {SemOp Val : Type}
    (sem : AttrSemantics SemOp Val) where
  documentId          : DocumentId
  atomId              : AtomId
  schema              : Digest
  operation           : OperationId
  author              : PrincipalRef
  height              : Height
  expectedRootCapId   : CapabilityId
  expectedIssuer      : IssuerId
  policyId            : PolicyId
  expectedPolicyEpoch : Epoch
  expectedIssuerEpoch : Epoch
  revoked             : Finset RevocationKey
  patchLen            : Nat
  saltedPatchRoot     : Digest
  claimedAst          : Val
  rootPolicy          : GrammarPolicy NT sem
  editPayload         : EditAtomPayload

/-- Executable check that an `EditAtomPayload` writes a sealed `Hyperdocument` atom in `documentId`
at `atomId` with schema `schema`, authored and wrapped by `(author, operation)`, ciphertext length
`patchLen`, and **empty cleartext payload** (`payload = []`, preserving `K-NARROW-HIDE`). -/
def checkSealedAtomEdit {NT SemOp Val : Type} {sem : AttrSemantics SemOp Val}
    (stmt : SealedHyperdocPatchStmt NT sem) : Bool :=
  decide (stmt.editPayload.atomId = stmt.atomId) &&
  decide (stmt.editPayload.before.document = stmt.documentId) &&
  stmt.editPayload.payload.isEmpty &&
  match stmt.editPayload.kind with
  | .sealedObject sc frag =>
      decide (sc = stmt.schema) &&
      decide (frag.author = stmt.author) &&
      decide (frag.operation = stmt.operation) &&
      decide (frag.wrappedBy = stmt.author) &&
      decide (frag.wrappedAt = stmt.operation) &&
      decide (frag.ciphertext.length = stmt.patchLen)
  | _ => false

theorem checkSealedAtomEdit_post_sealed {NT SemOp Val : Type} {sem : AttrSemantics SemOp Val}
    {stmt : SealedHyperdocPatchStmt NT sem}
    (hok : checkSealedAtomEdit stmt = true) :
    let postAtom := editAtomRecord stmt.operation stmt.editPayload
    postAtom.payload = [] ∧
    postAtom.kind.validPayload postAtom.payload = true ∧
    ∃ frag, postAtom.kind = .sealedObject stmt.schema frag ∧
      frag.author = stmt.author ∧ frag.operation = stmt.operation ∧
      frag.wrappedBy = stmt.author ∧ frag.wrappedAt = stmt.operation ∧
      frag.ciphertext.length = stmt.patchLen := by
  unfold checkSealedAtomEdit at hok
  cases hkind : stmt.editPayload.kind with
  | text => simp [hkind] at hok
  | inlineObject _ => simp [hkind] at hok
  | sealedObject sc frag =>
      rw [hkind] at hok
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff] at hok
      have hempty : stmt.editPayload.payload = [] := by tauto
      have hsc : sc = stmt.schema := by tauto
      have hauth : frag.author = stmt.author := by tauto
      have hop : frag.operation = stmt.operation := by tauto
      have hwby : frag.wrappedBy = stmt.author := by tauto
      have hwat : frag.wrappedAt = stmt.operation := by tauto
      have hclen : frag.ciphertext.length = stmt.patchLen := by tauto
      subst hsc
      refine ⟨hempty, ?_, frag, by simp [editAtomRecord, hkind], hauth, hop, hwby, hwat, hclen⟩
      simp [editAtomRecord, hkind, AtomKind.validPayload, hempty]

/-- Executable revocation & epoch-freshness check for one capability hop against `stmt`. -/
def checkCapFreshUnrevoked (revoked : Finset RevocationKey)
    (policyId : PolicyId) (expectedPolicyEpoch expectedIssuerEpoch : Epoch)
    (cap : Capability .object) : Bool :=
  decide (cap.policyId = policyId) &&
  decide (cap.policyEpoch = expectedPolicyEpoch) &&
  decide (cap.issuerEpoch = expectedIssuerEpoch) &&
  decide (RevocationKey.capability cap.id ∉ revoked) &&
  decide (∀ anc ∈ cap.ancestors, RevocationKey.capability anc ∉ revoked) &&
  decide (∀ ch ∈ cap.channels, RevocationKey.channel ch ∉ revoked)

/-- Executable edge check for capability delegation/attenuation `p → c`:
requires distinct IDs, transport `Capability.Attenuates`, AND either strict holder self-narrowing
(`c.holder.Narrows p.holder`) OR explicit delegation authority (`Verb.delegateObject` allowed by `p`
with non-bearer child holder), blocking non-delegatable leaf capability re-delegation. -/
def checkCapEdge (parentage : Parentage) (p c : Capability .object) : Bool :=
  decide (c.id ≠ p.id) &&
  decide (c.Attenuates p parentage) &&
  decide (c.holder.Narrows p.holder ∨
    ((Verb.delegateObject).AllowedBy p.scope.verbs ∧ c.holder ≠ .bearer))

/-- Executable multi-hop capability + `GrammarPolicy` chain checker:
verifies root-authority anchoring (`expectedRootCapId`, `expectedIssuer`, `parent = none`),
leaf scope coverage (`targets.Covers`, `.mutateObject`, `patchLen ≤ perRequestBytes`),
unrevoked & epoch-pinned hops, `checkCapEdge` + `grammarPolicyAttenuates` along every edge,
and leaf author binding within `[notBefore, notAfter]` at `stmt.height`. -/
def checkDelegatedCapChain {NT SemOp Val : Type}
    [DecidableEq NT] [DecidableEq SemOp]
    {sem : AttrSemantics SemOp Val}
    (parentage : Parentage)
    (stmt : SealedHyperdocPatchStmt NT sem)
    (chain : List (DelegatedGrammarHop NT sem)) : Bool :=
  match chain.head?, chain.getLast? with
  | some rootHop, some leafHop =>
      decide (rootHop.capability.id = stmt.expectedRootCapId) &&
      decide (rootHop.capability.issuer = stmt.expectedIssuer) &&
      decide (rootHop.capability.parent = none) &&
      decide (rootHop.capability.root = rootHop.capability.id) &&
      decide (rootHop.capability.ancestors = ∅) &&
      decide (stmt.author.capabilityKind = .object) &&
      decide (leafHop.capability.id = stmt.author.capabilityId) &&
      decide (leafHop.capability.holder = .subject stmt.author.subject) &&
      decide (leafHop.capability.notBefore ≤ stmt.height ∧ stmt.height ≤ leafHop.capability.notAfter) &&
      decide (leafHop.capability.scope.targets.Covers parentage ⟨stmt.documentId.digest.value⟩) &&
      decide ((Verb.mutateObject).AllowedBy leafHop.capability.scope.verbs) &&
      decide (stmt.patchLen ≤ leafHop.capability.scope.perRequestBytes) &&
      grammarPolicyAttenuates rootHop.policy stmt.rootPolicy &&
      chain.all (fun hop =>
        checkCapFreshUnrevoked stmt.revoked stmt.policyId
          stmt.expectedPolicyEpoch stmt.expectedIssuerEpoch hop.capability) &&
      policyChainAttenuates (chain.map DelegatedGrammarHop.policy) &&
      (let rec checkCapEdges : List (DelegatedGrammarHop NT sem) → Bool
        | [] => true
        | [_] => true
        | p :: c :: rest =>
            checkCapEdge parentage p.capability c.capability &&
            checkCapEdges (c :: rest)
       checkCapEdges chain)
  | _, _ => false

/-- Optional succinct `PrivateReceipt` guard proof for an `AutomatonBound` over `saltedPatchRoot`. -/
structure SuccinctGuardBundle (ell m fq : Nat) where
  bound   : AutomatonBound
  cert    : PrivateContentCert
  receipt : PrivateReceipt ell m fq

/-- Witness presented to `verifySealedHyperdocPatch`. -/
structure SealedHyperdocPatchWitness (NT SemOp : Type)
    {Val : Type} (sem : AttrSemantics SemOp Val)
    (ell m fq : Nat := 0) where
  chain          : List (DelegatedGrammarHop NT sem)
  patchBytes     : List UInt8
  patchSalts     : List Salt248
  ruleSeq        : List (AttrRule UInt8 NT SemOp)
  succinctGuards : List (SuccinctGuardBundle ell m fq) := []

/-- Executable check for any attached succinct `PrivateReceipt` guard bundles against
`(stmt.patchLen, stmt.saltedPatchRoot)`. -/
def checkSuccinctGuardBundles {NT SemOp Val : Type} {sem : AttrSemantics SemOp Val}
    {ell m fq : Nat}
    (stmt : SealedHyperdocPatchStmt NT sem)
    (bundles : List (SuccinctGuardBundle ell m fq)) : Bool :=
  bundles.all fun g =>
    g.bound.wellFormedB &&
    decide (g.cert.contentRoot = stmt.saltedPatchRoot) &&
    decide (g.cert.recordLength = stmt.patchLen) &&
    decide (g.cert.automatonRoot = automatonCommit (dfaToTable g.bound.dfa)) &&
    decide (g.cert.claim = boundToClaim g.bound) &&
    checkPrivate g.cert g.receipt

/-- **Executable Sealed `Hyperdocument` Blinded-Patch Gate (`verifySealedHyperdocPatch`)**:
verifies:
1. Sealed `.sealedObject` `Hyperdocument` atom edit with empty cleartext durable payload,
2. Epoch-pinned, unrevoked capability & `GrammarPolicy` delegation chain (`rootPolicy →* leafPolicy`),
3. Positive length + `Tower256` `saltedContentCommit` binding `(patchLen, saltedPatchRoot)`,
4. Leaf `PolicyAdmits` (`execPolicyVerify leafHop.policy patchBytes ruleSeq claimedAst`), and
5. Any attached succinct `Tower256PrivateContentCert` guard bundles. -/
def verifySealedHyperdocPatch {NT SemOp Val : Type}
    [DecidableEq NT] [DecidableEq SemOp] [DecidableEq Val]
    {sem : AttrSemantics SemOp Val}
    {ell m fq : Nat}
    (parentage : Parentage)
    (stmt : SealedHyperdocPatchStmt NT sem)
    (wit : SealedHyperdocPatchWitness NT SemOp sem ell m fq) : Bool :=
  match wit.chain.getLast? with
  | none => false
  | some leafHop =>
      decide (0 < stmt.patchLen) &&
      checkSealedAtomEdit stmt &&
      checkDelegatedCapChain parentage stmt wit.chain &&
      decide (wit.patchBytes.length = stmt.patchLen) &&
      decide (wit.patchSalts.length = stmt.patchLen) &&
      decide (saltedContentCommit wit.patchBytes wit.patchSalts = stmt.saltedPatchRoot) &&
      execPolicyVerify leafHop.policy wit.patchBytes wit.ruleSeq stmt.claimedAst &&
      checkSuccinctGuardBundles stmt wit.succinctGuards

/-! ## §3. Capstone Soundness Theorem (`verifySealedHyperdocPatch_sound_or_collision`) -/

/-- Named salted commitment relation for the sealed `Hyperdocument` patch cell. -/
def CommitsSaltedPatch {NT SemOp Val : Type} {sem : AttrSemantics SemOp Val}
    (stmt : SealedHyperdocPatchStmt NT sem)
    (wNamed : List UInt8) (sNamed : List Salt248) : Prop :=
  wNamed.length = stmt.patchLen ∧
  sNamed.length = stmt.patchLen ∧
  saltedContentCommit wNamed sNamed = stmt.saltedPatchRoot

/-- Explicit collision predicate extracting a concrete SP 800-185 `cSHAKE256` `FramedXofCollision`
from colliding salted patch trees. -/
theorem saltedCollision_is_framedXofCollision
    {w₁ : List UInt8} {s₁ : List Salt248} {w₂ : List UInt8} {s₂ : List Salt248}
    (h : SaltedCollision w₁ s₁ w₂ s₂) :
    let f := saltedCollisionFrames w₁ s₁ w₂ s₂
    FramedXofCollision cshakeC f.customization f.left f.right :=
  h

/-- **`verifySealedHyperdocPatch_sound_or_collision`** — Capstone Assurance Theorem:
Whenever `verifySealedHyperdocPatch parentage stmt wit = true`, for **any** salted payload
`(wNamed, sNamed)` committed at `(stmt.patchLen, stmt.saltedPatchRoot)`, **EITHER**:
1. **Full Root-Authority Policy Admission & Non-Escalation Holds on `wNamed`:**
   - `wNamed = wit.patchBytes` and `sNamed = wit.patchSalts`,
   - `PolicyAdmits stmt.rootPolicy wNamed wit.ruleSeq stmt.claimedAst`,
   - **Secret Absence & Padded Complement:** `wNamed = redactBytes stmt.rootPolicy.redactRules wNamed`
     and every `rt ∈ stmt.rootPolicy.redactRules` satisfies `AbsentPlain wNamed rt.pat` and
     `MatchesRegex wNamed (Regex.paddedComplement (Regex.literal rt.pat))`,
   - **Automaton Guards:** every `b ∈ stmt.rootPolicy.bounds` satisfies `b.holds wNamed = true` and
     `Dfaops.satisfiesClaim b.dfa.toDfaTable (boundToClaim b) wNamed = true`,
   - **Unique Authorized AST (`ast_root = ast_leaf = stmt.claimedAst`):**
     `wNamed ∈ stmt.rootPolicy.cfg.toCfg.language` and
     `∀ rs' ast', AttrReplay stmt.rootPolicy.cfg rs' wNamed ast' → ast' = stmt.claimedAst ∧ rs' = wit.ruleSeq`,
   - **Epoch-Pinned, Unrevoked, & Sealed Durable Cell:** every capability hop in `wit.chain` is
     epoch-current and unrevoked, and `editAtomRecord stmt.operation stmt.editPayload` writes a
     `.sealedObject` with empty cleartext `payload = []`;
2. **OR** an explicit SP 800-185 `cSHAKE256` `FramedXofCollision cshakeC` is constructively
   computed at `saltedCollisionFrames wit.patchBytes wit.patchSalts wNamed sNamed`! -/
theorem verifySealedHyperdocPatch_sound_or_collision {NT SemOp Val : Type}
    [DecidableEq NT] [DecidableEq SemOp] [DecidableEq Val]
    {sem : AttrSemantics SemOp Val}
    {ell m fq : Nat}
    (parentage : Parentage)
    (stmt : SealedHyperdocPatchStmt NT sem)
    (wit : SealedHyperdocPatchWitness NT SemOp sem ell m fq)
    (hver : verifySealedHyperdocPatch parentage stmt wit = true)
    (wNamed : List UInt8) (sNamed : List Salt248)
    (hcomm : CommitsSaltedPatch stmt wNamed sNamed) :
    (wNamed = wit.patchBytes ∧
     sNamed = wit.patchSalts ∧
     PolicyAdmits stmt.rootPolicy wNamed wit.ruleSeq stmt.claimedAst ∧
     (∀ rt ∈ stmt.rootPolicy.redactRules,
       AbsentPlain wNamed rt.pat ∧
       MatchesRegex wNamed (Regex.paddedComplement (Regex.literal rt.pat))) ∧
     (∀ b ∈ stmt.rootPolicy.bounds,
       b.holds wNamed = true ∧
       Dfaops.satisfiesClaim (dfaToTable b.dfa) (boundToClaim b) wNamed = true) ∧
     wNamed ∈ stmt.rootPolicy.cfg.toCfg.language ∧
     (∀ (rs' : List (AttrRule UInt8 NT SemOp)) (ast' : Val),
       AttrReplay stmt.rootPolicy.cfg rs' wNamed ast' →
       ast' = stmt.claimedAst ∧ rs' = wit.ruleSeq) ∧
     (∀ hop ∈ wit.chain,
       hop.capability.policyEpoch = stmt.expectedPolicyEpoch ∧
       hop.capability.issuerEpoch = stmt.expectedIssuerEpoch ∧
       RevocationKey.capability hop.capability.id ∉ stmt.revoked) ∧
     (∃ rootHop leafHop,
       wit.chain.head? = some rootHop ∧
       wit.chain.getLast? = some leafHop ∧
       rootHop.capability.id = stmt.expectedRootCapId ∧
       rootHop.capability.issuer = stmt.expectedIssuer ∧
       rootHop.capability.parent = none ∧
       leafHop.capability.scope.targets.Covers parentage ⟨stmt.documentId.digest.value⟩ ∧
       (Verb.mutateObject).AllowedBy leafHop.capability.scope.verbs ∧
       stmt.patchLen ≤ leafHop.capability.scope.perRequestBytes) ∧
     (editAtomRecord stmt.operation stmt.editPayload).payload = []) ∨
    (let f := saltedCollisionFrames wit.patchBytes wit.patchSalts wNamed sNamed
     FramedXofCollision cshakeC f.customization f.left f.right) := by
  unfold verifySealedHyperdocPatch at hver
  cases hlast : wit.chain.getLast? with
  | none => rw [hlast] at hver; simp at hver
  | some leafHop =>
      rw [hlast] at hver
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hver
      rcases hver with ⟨⟨⟨⟨⟨⟨⟨_, hseal⟩, hchain⟩, hwLen⟩, hsLen⟩, hsRoot⟩, hexecLeaf⟩, _⟩
      rcases hcomm with ⟨hnLen, hnsLen, hnRoot⟩
      rcases saltedRoot_eq_or_collision wit.patchBytes wit.patchSalts wNamed sNamed
          (hsLen.trans hwLen.symm) (hnsLen.trans hnLen.symm) (hwLen.trans hnLen.symm)
          (hsRoot.trans hnRoot.symm) with ⟨hweq, hseq⟩ | hcol
      · left
        subst hweq hseq
        have hadmLeaf : PolicyAdmits leafHop.policy wit.patchBytes wit.ruleSeq stmt.claimedAst :=
          (execPolicyVerify_iff _ _ _ _).mp hexecLeaf
        unfold checkDelegatedCapChain at hchain
        cases hhead : wit.chain.head? with
        | none => rw [hhead] at hchain; simp at hchain
        | some rootHop =>
            rw [hhead, hlast] at hchain
            simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hchain
            have hrootId : rootHop.capability.id = stmt.expectedRootCapId := by tauto
            have hrootIss : rootHop.capability.issuer = stmt.expectedIssuer := by tauto
            have hrootPar : rootHop.capability.parent = none := by tauto
            have hcovTgt : leafHop.capability.scope.targets.Covers parentage ⟨stmt.documentId.digest.value⟩ := by tauto
            have hcovVerb : (Verb.mutateObject).AllowedBy leafHop.capability.scope.verbs := by tauto
            have hcovCost : stmt.patchLen ≤ leafHop.capability.scope.perRequestBytes := by tauto
            have hrootAtt : grammarPolicyAttenuates rootHop.policy stmt.rootPolicy = true := by tauto
            have hallFresh : ∀ hop ∈ wit.chain,
                checkCapFreshUnrevoked stmt.revoked stmt.policyId
                  stmt.expectedPolicyEpoch stmt.expectedIssuerEpoch hop.capability = true := by tauto
            have hpolChain : policyChainAttenuates (wit.chain.map DelegatedGrammarHop.policy) = true := by tauto
            have hpolHead : (wit.chain.map DelegatedGrammarHop.policy).head? = some rootHop.policy := by
              simp [List.head?_map, hhead]
            have hpolLast : (wit.chain.map DelegatedGrammarHop.policy).getLast? = some leafHop.policy := by
              simp [List.getLast?_map, hlast]
            have hadmRootHop := (policyChainAttenuates_sound hpolHead hpolLast hpolChain hadmLeaf).1
            obtain ⟨hadmRoot, habsRoot, hlangRoot, huniqRoot⟩ :=
              grammarPolicyAttenuates_sound hrootAtt hadmRootHop
            have hpostSeal := checkSealedAtomEdit_post_sealed hseal
            refine ⟨rfl, rfl, hadmRoot, ?_, ?_, hlangRoot, huniqRoot, ?_,
              ⟨rootHop, leafHop, hhead, hlast, hrootId, hrootIss, hrootPar, hcovTgt, hcovVerb, hcovCost⟩,
              hpostSeal.1⟩
            · intro rt hrt
              have habsW := habsRoot rt hrt
              exact ⟨(absentW_iff_plain _ _).mp habsW,
                     (absentW_iff_padded_complement _ _).mp habsW⟩
            · intro b hb
              have hbh := hadmRoot.2.2.2.1 b hb
              exact ⟨hbh, by rwa [satisfiesClaim_boundToClaim_eq]⟩
            · intro hop hhop
              have hf := hallFresh hop hhop
              unfold checkCapFreshUnrevoked at hf
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hf
              exact ⟨by tauto, by tauto, by tauto⟩
      · exact Or.inr (saltedCollision_is_framedXofCollision hcol)

/-- **Root-Only Observer Succinct Guard Theorem (`succinctGuardBundle_sound_or_miss_or_collision`):**
When an observer verifies ONLY a succinct `SuccinctGuardBundle` (without seeing `patchBytes` or
`patchSalts` in the clear!) alongside `grammarPolicyAttenuates leafPolicy rootPolicy = true`, any
committed salted payload `(wNamed, sNamed)` satisfies the `leafPolicy` guard (and any `rootPolicy`
guard entailed by it), OR hits `StepSamplingMiss`, OR exposes an explicit `PrivateCertCollision`. -/
theorem succinctGuardBundle_sound_or_miss_or_collision {NT SemOp Val : Type}
    {sem : AttrSemantics SemOp Val}
    {ell m fq : Nat}
    (stmt : SealedHyperdocPatchStmt NT sem)
    (g : SuccinctGuardBundle ell m fq)
    (bp : AutomatonBound)
    (hent : automatonBoundEntails g.bound bp = true)
    (hbundle : checkSuccinctGuardBundles stmt [g] = true)
    (wNamed : List UInt8) (sNamed : List Salt248)
    (hcomm : CommitsSaltedPatch stmt wNamed sNamed)
    (rows : List TraceRow) (hrowsLen : rows.length = g.cert.recordLength)
    (hrowsWb : ∀ row ∈ rows, row.WellBounded)
    (hrowsRoot : traceCommit rows = g.receipt.traceRoot)
    (T : RawTranscript (rawPcs ell))
    (hcons : ∀ (hm : m ≤ ell) (hell : ell ≤ 256),
      let sFri := friStatementOf g.cert g.receipt.friInitialRoot hm hell
      Consistent sFri.denote (g.receipt.friReceipt.denote sFri) T) :
    (g.bound.holds wNamed = true ∧ bp.holds wNamed = true) ∨
    StepSamplingMiss g.cert (dfaToTable g.bound.dfa) wNamed rows g.receipt ∨
    ∃ (hm : m ≤ ell) (hell : ell ≤ 256),
      PrivateCertCollision g.cert g.receipt hm hell (dfaToTable g.bound.dfa) wNamed sNamed rows T := by
  unfold checkSuccinctGuardBundles at hbundle
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq] at hbundle
  rcases hbundle with ⟨⟨⟨⟨⟨hwfB, hcRoot⟩, hcLen⟩, haRoot⟩, hclaimEq⟩, hpriv⟩
  have hwfTable : (dfaToTable g.bound.dfa).WellFormed :=
    dfaSpec_wellFormed_toDfaTable (AutomatonBound.dfa_wellFormed_of_wellFormedB hwfB)
  have hNamedPriv : CommitsPrivate g.cert (dfaToTable g.bound.dfa) wNamed sNamed :=
    ⟨hwfTable, haRoot.symm, hcomm.1.trans hcLen.symm, hcomm.2.1.trans hcLen.symm,
     hcomm.2.2.trans hcRoot.symm⟩
  obtain ⟨hm, hell, _, _, hdisj⟩ := checkPrivate_sound_or_collision g.cert g.receipt hpriv
    (dfaToTable g.bound.dfa) wNamed sNamed hNamedPriv rows hrowsLen hrowsWb hrowsRoot T hcons
  rcases hdisj with ⟨⟨_, _, hsat⟩, _⟩ | hmiss | hcol
  · left
    rw [hclaimEq, satisfiesClaim_boundToClaim_eq] at hsat
    exact ⟨hsat, automatonBoundEntails_sound hent wNamed hsat⟩
  · exact Or.inr (Or.inl hmiss)
  · exact Or.inr (Or.inr ⟨hm, hell, hcol⟩)

/-! ## §4. Concrete 3-Hop Witness Inhabitation, Refusal Teeth, & JSON Conformance Emitter -/

def demoParentage : Parentage := Parentage.empty

def demoRootCap : Capability .object where
  id          := ⟨100⟩
  root        := ⟨100⟩
  parent      := none
  issuer      := ⟨1⟩
  holder      := .subject ⟨10⟩
  scope       := { targets := .explicit {⟨500⟩}, verbs := {.mutateObject, .delegateObject}, perRequestBytes := 1000 }
  notBefore   := 1
  notAfter    := 100
  issuerEpoch := 7
  policyId    := ⟨42⟩
  policyEpoch := 3
  ancestors   := ∅
  channels    := {⟨9⟩}

def demoServiceCap : Capability .object where
  id          := ⟨101⟩
  root        := ⟨100⟩
  parent      := some ⟨100⟩
  issuer      := ⟨1⟩
  holder      := .subject ⟨20⟩
  scope       := { targets := .explicit {⟨500⟩}, verbs := {.mutateObject, .delegateObject}, perRequestBytes := 500 }
  notBefore   := 5
  notAfter    := 80
  issuerEpoch := 7
  policyId    := ⟨42⟩
  policyEpoch := 3
  ancestors   := {⟨100⟩}
  channels    := {⟨9⟩}

def demoSubagentCap : Capability .object where
  id          := ⟨102⟩
  root        := ⟨100⟩
  parent      := some ⟨101⟩
  issuer      := ⟨1⟩
  holder      := .subject ⟨30⟩
  scope       := { targets := .explicit {⟨500⟩}, verbs := {.mutateObject}, perRequestBytes := 128 }
  notBefore   := 10
  notAfter    := 50
  issuerEpoch := 7
  policyId    := ⟨42⟩
  policyEpoch := 3
  ancestors   := {⟨101⟩, ⟨100⟩}
  channels    := {⟨9⟩}

def demoAuthor : PrincipalRef where
  subject        := ⟨30⟩
  capabilityKind := .object
  capabilityId   := ⟨102⟩

def demoDocId : DocumentId := ⟨⟨500⟩⟩
def demoAtomId : AtomId := ⟨⟨501⟩⟩
def demoOpId : OperationId := ⟨⟨9001⟩⟩
def demoSchema : Digest := ⟨777⟩

def demoBeforeAtom : AtomRecord where
  document     := demoDocId
  kind         := .sealedObject demoSchema
    { ciphertext := [0xAA, 0xBB], wrapping := [0x11],
      author := demoAuthor, operation := ⟨⟨9000⟩⟩,
      wrappedBy := demoAuthor, wrappedAt := ⟨⟨9000⟩⟩ }
  payload      := []
  createdBy    := demoAuthor
  createdAt    := ⟨⟨9000⟩⟩
  revision     := ⟨⟨9000⟩⟩
  tombstonedAt := none

def demoEditPayload : EditAtomPayload where
  atomId    := demoAtomId
  before    := demoBeforeAtom
  kind      := .sealedObject demoSchema
    { ciphertext := List.replicate sampleSubagentPayload.length 0xAA,
      wrapping := List.replicate 32 0x22,
      author := demoAuthor, operation := demoOpId,
      wrappedBy := demoAuthor, wrappedAt := demoOpId }
  payload   := []
  tombstone := false

def demoSalts : List Salt248 :=
  (List.range sampleSubagentPayload.length).map fun i =>
    ⟨(0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d + 7919 * (i + 1)) % 2 ^ 248,
      Nat.mod_lt _ (by positivity)⟩

def demoStmt : SealedHyperdocPatchStmt CapNT capSemantics where
  documentId          := demoDocId
  atomId              := demoAtomId
  schema              := demoSchema
  operation           := demoOpId
  author              := demoAuthor
  height              := 25
  expectedRootCapId   := ⟨100⟩
  expectedIssuer      := ⟨1⟩
  policyId            := ⟨42⟩
  expectedPolicyEpoch := 3
  expectedIssuerEpoch := 7
  revoked             := ∅
  patchLen            := sampleSubagentPayload.length
  saltedPatchRoot     := saltedContentCommit sampleSubagentPayload demoSalts
  claimedAst          := expectedSubagentAst
  rootPolicy          := rootCapPolicy
  editPayload         := demoEditPayload

def demoChain : List (DelegatedGrammarHop CapNT capSemantics) :=
  [ ⟨demoRootCap, rootCapPolicy⟩,
    ⟨demoServiceCap, serviceCapPolicy⟩,
    ⟨demoSubagentCap, subagentToolCapPolicy⟩ ]

def demoWitness : SealedHyperdocPatchWitness CapNT CapOp capSemantics 0 0 0 where
  chain          := demoChain
  patchBytes     := sampleSubagentPayload
  patchSalts     := demoSalts
  ruleSeq        := sampleSubagentRuleSeq
  succinctGuards := []

set_option maxRecDepth 40000 in
/-- **Symbolic Completeness / Premise Inhabitation (`demo_sealedHyperdocGate_verified`)**:
proves `verifySealedHyperdocPatch demoParentage demoStmt demoWitness = true` without unfolding
Keccak-f in the kernel! -/
theorem demo_sealedHyperdocGate_verified :
    verifySealedHyperdocPatch demoParentage demoStmt demoWitness = true := by
  have hlenPos : decide (0 < demoStmt.patchLen) = true := by decide
  have hseal : checkSealedAtomEdit demoStmt = true := by decide
  have hchain : checkDelegatedCapChain demoParentage demoStmt demoWitness.chain = true := by
    change checkDelegatedCapChain demoParentage demoStmt demoChain = true
    unfold checkDelegatedCapChain
    have hch := threeHop_delegation_verified.2.2.1
    have hrr : grammarPolicyAttenuates rootCapPolicy rootCapPolicy = true :=
      grammarPolicyAttenuates_refl (by decide)
    have hat1 : checkCapEdge demoParentage demoRootCap demoServiceCap = true := by decide
    have hat2 : checkCapEdge demoParentage demoServiceCap demoSubagentCap = true := by decide
    simp only [demoChain, List.head?_cons, List.getLast?_cons_cons,
      List.getLast?_singleton, hrr, hch, hat1, hat2, checkDelegatedCapChain.checkCapEdges,
      List.map_cons, List.map_nil]
    decide
  have hexec : execPolicyVerify subagentToolCapPolicy demoWitness.patchBytes
      demoWitness.ruleSeq demoStmt.claimedAst = true :=
    (execPolicyVerify_iff _ _ _ _).mpr threeHop_delegation_verified.2.2.2.1
  have hlast : demoWitness.chain.getLast? = some ⟨demoSubagentCap, subagentToolCapPolicy⟩ := rfl
  have hwlen : decide (demoWitness.patchBytes.length = demoStmt.patchLen) = true := by decide
  have hslen : decide (demoWitness.patchSalts.length = demoStmt.patchLen) = true := by decide
  have hsroot : decide (saltedContentCommit demoWitness.patchBytes demoWitness.patchSalts =
      demoStmt.saltedPatchRoot) = true := decide_eq_true rfl
  have hsucc : checkSuccinctGuardBundles demoStmt demoWitness.succinctGuards = true := rfl
  unfold verifySealedHyperdocPatch
  rw [hlast]
  simp only [hlenPos, hseal, hchain, hwlen, hslen, hsroot, hexec, hsucc, Bool.and_self]

/-- **Assurance Refusal Tooth 1 (Revoked Intermediate TeamLead Capability Rejected):**
revoking `demoServiceCap.id` (`⟨101⟩`) immediately rejects the downstream subagent's patch! -/
theorem demo_refuses_revoked_intermediate :
    verifySealedHyperdocPatch demoParentage
      { demoStmt with revoked := {RevocationKey.capability ⟨101⟩} } demoWitness = false := by
  have hbad : checkCapFreshUnrevoked {RevocationKey.capability ⟨101⟩} ⟨42⟩ 3 7 demoServiceCap = false := by
    decide
  unfold verifySealedHyperdocPatch checkDelegatedCapChain
  simp [demoWitness, demoChain, hbad]

/-- **Assurance Refusal Tooth 2 (Stale Policy Epoch Rejected):**
rotating `expectedPolicyEpoch` from `3` to `4` immediately rejects the patch! -/
theorem demo_refuses_stale_policy_epoch :
    verifySealedHyperdocPatch demoParentage
      { demoStmt with expectedPolicyEpoch := 4 } demoWitness = false := by
  have hbad : checkCapFreshUnrevoked ∅ ⟨42⟩ 4 7 demoRootCap = false := by decide
  unfold verifySealedHyperdocPatch checkDelegatedCapChain
  simp [demoWitness, demoChain, hbad]

/-- **Assurance Refusal Tooth 3 (Cleartext Leak in Durable `Hyperdocument` Atom Rejected):**
any non-empty cleartext `payload` on a `.sealedObject` atom is refused by `checkSealedAtomEdit`! -/
theorem demo_refuses_cleartext_atom_payload :
    verifySealedHyperdocPatch demoParentage
      { demoStmt with editPayload := { demoEditPayload with payload := [0x41] } } demoWitness = false := by
  have hbad : checkSealedAtomEdit
      { demoStmt with editPayload := { demoEditPayload with payload := [0x41] } } = false := by
    decide
  unfold verifySealedHyperdocPatch
  simp [demoWitness, demoChain, hbad]

/-- Unauthorized 4th-hop capability minted from non-delegatable `demoSubagentCap` (`verbs = {.mutateObject}`)
for a distinct subject `⟨99⟩`. -/
def demoUnauthorizedFourthHopCap : Capability .object :=
  { demoSubagentCap with
    id := ⟨103⟩
    parent := some ⟨102⟩
    holder := .subject ⟨99⟩
    ancestors := {⟨102⟩, ⟨101⟩, ⟨100⟩} }

/-- **Assurance Refusal Tooth 4 (Non-Delegatable Leaf Re-Delegation Escalation Rejected):**
`demoSubagentCap` lacks `Verb.delegateObject`, so `checkCapEdge` refuses re-delegation to subject `⟨99⟩`! -/
theorem demo_refuses_non_delegatable_redelegation :
    checkCapEdge demoParentage demoSubagentCap demoUnauthorizedFourthHopCap = false := by
  decide

/-! ## §5. Pure-`Init` Conformance JSON Emitter (`prover/testdata/grammar_capability_conformance.json`) -/

private def hexBytes (bytes : List UInt8) : String :=
  String.join (bytes.map fun b =>
    let d := "0123456789abcdef".toList
    String.ofList [d[(b.toNat / 16)]!, d[(b.toNat % 16)]!])

private def natFixedLE (len val : Nat) : List UInt8 :=
  (List.range len).map fun i => UInt8.ofNat ((val / 256 ^ i) % 256)

private def digestHex (d : Digest) : String :=
  hexBytes (natFixedLE 32 d.value)

private def jsonBool (b : Bool) : String := if b then "true" else "false"

private def jsonStrList (xs : List String) : String :=
  "[" ++ String.intercalate ", " (xs.map fun s => "\"" ++ s ++ "\"") ++ "]"

private def jsonNatList (xs : List Nat) : String :=
  "[" ++ String.intercalate ", " (xs.map toString) ++ "]"

private def emitGrammarCapConformance (path : System.FilePath) : IO Unit := do
  let okGate := verifySealedHyperdocPatch demoParentage demoStmt demoWitness
  let cexSk := dfaCounterexample? acceptAllDfa noSkDashDfa
  let cexSqlVsSk := dfaCounterexample? noSqlDropDfa noSkDashDfa
  let cexShell := dfaCounterexample? acceptAllDfa noShellSubDfa
  unless okGate && cexSk == some (asciiBytes "sk-") &&
      cexSqlVsSk == some (asciiBytes "sk-") && cexShell == some (asciiBytes "$(") do
    throw (IO.userError "SealedHyperdocGrammarGate build-time self-check failed")
  let ruleIndices := sampleSubagentRuleSeq.map (fun r => subagentToolCapPolicy.rules.idxOf r)
  let json :=
    "{\n" ++
    "  \"schema\": \"minidregg.grammar_capability_conformance.v1\",\n" ++
    "  \"source\": \"Assurance/SealedHyperdocGrammarGate.lean\",\n" ++
    s!"  \"root_rule_count\": {rootCapPolicy.rules.length},\n" ++
    s!"  \"service_rule_count\": {serviceCapPolicy.rules.length},\n" ++
    s!"  \"subagent_rule_count\": {subagentToolCapPolicy.rules.length},\n" ++
    s!"  \"subagent_attenuates_service\": {jsonBool (grammarPolicyAttenuates subagentToolCapPolicy serviceCapPolicy)},\n" ++
    s!"  \"service_attenuates_root\": {jsonBool (grammarPolicyAttenuates serviceCapPolicy rootCapPolicy)},\n" ++
    s!"  \"three_hop_chain_valid\": {jsonBool (policyChainAttenuates [rootCapPolicy, serviceCapPolicy, subagentToolCapPolicy])},\n" ++
    s!"  \"tooth_widen_range_refused\": {jsonBool (!grammarPolicyAttenuates escalatedRangeCap serviceCapPolicy)},\n" ++
    s!"  \"tooth_drop_sk_refused\": {jsonBool (!grammarPolicyAttenuates droppedSkGuardCap serviceCapPolicy)},\n" ++
    s!"  \"tooth_wipe_prod_refused\": {jsonBool (!grammarPolicyAttenuates wipeProdEscalatedCap serviceCapPolicy)},\n" ++
    s!"  \"tooth_dup_key_refused\": {jsonBool (!grammarPolicyAttenuates dupKeyAmbigChildCap dupKeyParentCap)},\n" ++
    s!"  \"cex_accept_all_vs_no_sk_hex\": \"{hexBytes (cexSk.getD [])}\",\n" ++
    s!"  \"cex_no_sql_vs_no_sk_hex\": \"{hexBytes (cexSqlVsSk.getD [])}\",\n" ++
    s!"  \"cex_accept_all_vs_no_shell_hex\": \"{hexBytes (cexShell.getD [])}\",\n" ++
    s!"  \"no_sk_automaton_root\": \"{digestHex (automatonCommit (dfaToTable noSkDashDfa))}\",\n" ++
    s!"  \"no_sql_automaton_root\": \"{digestHex (automatonCommit (dfaToTable noSqlDropDfa))}\",\n" ++
    s!"  \"no_shell_automaton_root\": \"{digestHex (automatonCommit (dfaToTable noShellSubDfa))}\",\n" ++
    s!"  \"count_brace_automaton_root\": \"{digestHex (automatonCommit (dfaToTable countOpBraceDfa))}\",\n" ++
    s!"  \"patch_payload_hex\": \"{hexBytes sampleSubagentPayload}\",\n" ++
    s!"  \"patch_len\": {sampleSubagentPayload.length},\n" ++
    s!"  \"salts_hex\": {jsonStrList (demoSalts.map fun s => hexBytes (natFixedLE 31 s.val))},\n" ++
    s!"  \"salted_patch_root\": \"{digestHex demoStmt.saltedPatchRoot}\",\n" ++
    s!"  \"subagent_rule_indices\": {jsonNatList ruleIndices},\n" ++
    "  \"expected_ast\": {\n" ++
    s!"    \"tool_hex\": \"{hexBytes (asciiBytes "patch_atom")}\",\n" ++
    s!"    \"target_hex\": \"{hexBytes (asciiBytes "sandbox/note_01")}\",\n" ++
    "    \"amount\": 3\n" ++
    "  }\n" ++
    "}\n"
  if let some dir := path.parent then IO.FS.createDirAll dir
  IO.FS.writeFile path json

#eval emitGrammarCapConformance "prover/testdata/grammar_capability_conformance.json"

/-! ## §6. Axiom Audit (`#guard_msgs` Pins) -/

/-- info: 'Minidregg.Assurance.SealedHyperdocGrammarGate.satisfiesClaim_boundToClaim_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms satisfiesClaim_boundToClaim_eq

/-- info: 'Minidregg.Assurance.SealedHyperdocGrammarGate.verifySealedHyperdocPatch_sound_or_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms verifySealedHyperdocPatch_sound_or_collision

/-- info: 'Minidregg.Assurance.SealedHyperdocGrammarGate.succinctGuardBundle_sound_or_miss_or_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms succinctGuardBundle_sound_or_miss_or_collision

/-- info: 'Minidregg.Assurance.SealedHyperdocGrammarGate.demo_sealedHyperdocGate_verified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms demo_sealedHyperdocGate_verified

/-- info: 'Minidregg.Assurance.SealedHyperdocGrammarGate.demo_refuses_revoked_intermediate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms demo_refuses_revoked_intermediate

/-- info: 'Minidregg.Assurance.SealedHyperdocGrammarGate.demo_refuses_stale_policy_epoch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms demo_refuses_stale_policy_epoch

/-- info: 'Minidregg.Assurance.SealedHyperdocGrammarGate.demo_refuses_cleartext_atom_payload' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms demo_refuses_cleartext_atom_payload

/-- info: 'Minidregg.Assurance.SealedHyperdocGrammarGate.demo_refuses_non_delegatable_redelegation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms demo_refuses_non_delegatable_redelegation

end Minidregg.Assurance.SealedHyperdocGrammarGate
