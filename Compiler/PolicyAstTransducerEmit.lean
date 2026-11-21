/-
# `Compiler/PolicyAstTransducerEmit.lean` — Content-Bound `RewriteCert` + LL(1) AST Extraction Bridge & Conformance Seam

Welds `Theory/VerifiedAstTransducer.lean` (`AttrCfg`, `ll1Deterministic`, `attrReplay_unique_of_ll1`,
`redactBytes`, `redactBytes_scrubs_all`, `redactBytes_preserves_clean`) to:
1. `Selvage/ContentCertificate.lean` (`AbsentPlain`, `OccursInPlain`, `SubstringAtPlain`, and
   Brzozowski padded-complement `Regex.paddedComplement`), and
2. `Compiler/Tower256ContentCert.lean` (`contentCommit` over real SP 800-185 `cSHAKE256` cube-Merkle
   trees and explicit `DenseCollision` / `FramedXofCollision`).

## Core Theorems (`0 sorry`, `0 axiom`, `0 native_decide`, `0 #guard`)

- **`absentW_iff_padded_complement` & `redactBytes_scrubs_padded_complement`:**
  Every secret pattern `rt.pat` (`rt ∈ rules`) under `allRulesSafe rules = true` is provably
  `AbsentPlain` from `redactBytes rules w` and accepted by `Regex.derives _ (Regex.paddedComplement (Regex.literal rt.pat))`.
- **`rewrite_and_extract_sound_or_collision`:**
  Given committed raw agent transcript `(rawLength, rawRoot)`, committed sanitized transcript
  `(cleanLength, cleanRoot)`, and public extracted AST `claimedAst`, an accepted `RewriteCertWitness`
  proves on ANY `(wRaw, wClean)` matching those commitments that:
  1. `wClean = redactBytes rules wRaw` (canonical deterministic sanitization) & `RedactsTo rules wRaw wClean`,
  2. every pattern `rt.pat` (`rt ∈ rules`) is `AbsentPlain` and matches `Regex.paddedComplement` on `wClean`,
  3. clean raw transcripts (`∀ r ∈ rules, AbsentPlain wRaw r.pat`) satisfy `wClean = wRaw`,
  4. `AttrReplay g wit.ruleSeq wClean stmt.claimedAst` and `wClean ∈ g.toCfg.language`, AND
  5. **Unique AST & Parse (`∀ rs' ast', AttrReplay g rs' wClean ast' → ast' = stmt.claimedAst ∧ rs' = wit.ruleSeq`)** —
  OR constructively exhibits an explicit `cSHAKE256` `DenseCollision` (`FramedXofCollision cshakeC`)!

Authors `prover/testdata/policy_transducer_conformance.json` via `#eval`; Lean is the sole author.
-/
import Theory.VerifiedAstTransducer
import Selvage.ContentCertificate
import Compiler.Tower256ContentCert
import Lean.Data.Json

namespace Minidregg.Compiler.PolicyAstTransducerEmit

open Minidregg.Theory.VerifiedAstTransducer
open Minidregg.Selvage
open Minidregg.Compiler.Tower256ContentCert
open Minidregg.Compiler.Tower256CoordinateMerkle (cshakeC)
open Minidregg.Theory.TypedAuthorization (Digest)
open Lean (Json ToJson toJson)

set_option autoImplicit false

/-! ## §1. Bridge Between `Theory.VerifiedAstTransducer` and `Selvage.ContentCertificate` -/

theorem substringAtW_iff_plain {Sym : Type} (w : List Sym) (i : Nat) (P : List Sym) :
    SubstringAtW w i P ↔ SubstringAtPlain w i P :=
  (substringAtPlain_iff_take_drop w i P).symm

theorem occursInW_iff_plain {Sym : Type} (w P : List Sym) :
    OccursInW w P ↔ OccursInPlain w P :=
  exists_congr fun i => substringAtW_iff_plain w i P

theorem absentW_iff_plain {Sym : Type} (w P : List Sym) :
    AbsentW w P ↔ AbsentPlain w P :=
  forall_congr' fun i => not_congr (substringAtW_iff_plain w i P)

theorem absentW_iff_padded_complement {Sym : Type} (w P : List Sym) :
    AbsentW w P ↔ MatchesRegex w (Regex.paddedComplement (Regex.literal P)) := by
  rw [absentW_iff_plain]
  change AbsentPlain w P ↔ ¬ MatchesRegex w (Regex.pad (Regex.literal P))
  exact absent_iff_padded_complement w P

theorem absentW_iff_derives_padded_complement {Sym : Type} [DecidableEq Sym]
    (w P : List Sym) :
    AbsentW w P ↔ Regex.derives w (Regex.paddedComplement (Regex.literal P)) = true := by
  rw [absentW_iff_plain]
  exact absent_iff_derives_padded_complement w P

/-- **Sanitizer-to-Padded-Complement Bridge (`redactBytes_scrubs_padded_complement`):**
Under `allRulesSafe rules = true`, for every `rt ∈ rules` and every raw transcript `w`,
`redactBytes rules w` satisfies `Selvage.AbsentPlain`, `MatchesRegex _ (paddedComplement _)`,
and `Regex.derives _ (paddedComplement _) = true`. -/
theorem redactBytes_scrubs_padded_complement {Sym : Type} [DecidableEq Sym]
    (rules : List (RedactRule Sym)) (hsafe : allRulesSafe rules = true)
    (rt : RedactRule Sym) (hrt : rt ∈ rules) (w : List Sym) :
    AbsentPlain (redactBytes rules w) rt.pat ∧
    MatchesRegex (redactBytes rules w) (Regex.paddedComplement (Regex.literal rt.pat)) ∧
    Regex.derives (redactBytes rules w) (Regex.paddedComplement (Regex.literal rt.pat)) = true := by
  have hunpack := allRulesSafe_unpack hsafe rt hrt
  have habsW : AbsentW (redactBytes rules w) rt.pat :=
    redactBytes_scrubs_all rules rt hrt hunpack.1 hunpack.2 w
  exact ⟨(absentW_iff_plain _ _).mp habsW,
         (absentW_iff_padded_complement _ _).mp habsW,
         (absentW_iff_derives_padded_complement _ _).mp habsW⟩

/-- `Selvage.AbsentPlain` clean-input bridge: clean inputs suffer zero mangling. -/
theorem redactBytes_preserves_clean_plain {Sym : Type} [DecidableEq Sym]
    (rules : List (RedactRule Sym)) (w : List Sym)
    (hclean : ∀ r ∈ rules, AbsentPlain w r.pat) :
    redactBytes rules w = w :=
  redactBytes_preserves_clean rules w fun r hr => (absentW_iff_plain w r.pat).mpr (hclean r hr)

/-! ## §2. Content-Bound `RewriteCert` + LL(1) AST Extraction over `cSHAKE256` (`contentCommit`) -/

/-- Public content-bound statement binding `(rawLength, rawRoot)`, `(cleanLength, cleanRoot)`,
and extracted AST `claimedAst`. Including lengths alongside `contentCommit` eliminates the
trailing-zero dense-column root alias (`Tower256ContentCert.lean:622`). -/
structure RewriteCertStmt (Val : Type) where
  rawRoot     : Digest
  rawLength   : Nat
  cleanRoot   : Digest
  cleanLength : Nat
  claimedAst  : Val
  deriving DecidableEq, Repr

/-- Witness for `RewriteCertStmt`: raw bytes, sanitized bytes, and compact leftmost rule sequence. -/
structure RewriteCertWitness (NT SemOp : Type) where
  wRaw    : List UInt8
  wClean  : List UInt8
  ruleSeq : List (AttrRule UInt8 NT SemOp)
  deriving DecidableEq, Repr

/-- Honest statement constructor from concrete `(wRaw, wClean, ast)`. -/
def stmtForRewrite {Val : Type} (wRaw wClean : List UInt8) (ast : Val) : RewriteCertStmt Val where
  rawRoot     := contentCommit wRaw
  rawLength   := wRaw.length
  cleanRoot   := contentCommit wClean
  cleanLength := wClean.length
  claimedAst  := ast

/-- Named raw and sanitized byte records committed by `stmt`. -/
def CommitsRewritePair {Val : Type} (stmt : RewriteCertStmt Val) (wRaw wClean : List UInt8) : Prop :=
  wRaw.length = stmt.rawLength ∧ contentCommit wRaw = stmt.rawRoot ∧
  wClean.length = stmt.cleanLength ∧ contentCommit wClean = stmt.cleanRoot

/-- **Executable `RewriteCert` + LL(1) AST Extraction Verifier (`verifyRewriteAndExtract`)**:
checks grammar LL(1) determinacy, redaction policy safety, `cSHAKE256` root + length bindings on
both `wRaw` and `wClean`, exact deterministic sanitization `wClean = redactBytes rules wRaw`,
and linear-time attributed replay `execAttrReplay g wit.ruleSeq wit.wClean = some stmt.claimedAst`. -/
def verifyRewriteAndExtract {NT SemOp Val : Type}
    [DecidableEq NT] [DecidableEq SemOp] [DecidableEq Val]
    (g : AttrCfg UInt8 NT SemOp Val) (rules : List (RedactRule UInt8))
    (stmt : RewriteCertStmt Val) (wit : RewriteCertWitness NT SemOp) : Bool :=
  ll1Deterministic g &&
  allRulesSafe rules &&
  decide (wit.wRaw.length = stmt.rawLength) &&
  decide (contentCommit wit.wRaw = stmt.rawRoot) &&
  decide (wit.wClean.length = stmt.cleanLength) &&
  decide (contentCommit wit.wClean = stmt.cleanRoot) &&
  decide (wit.wClean = redactBytes rules wit.wRaw) &&
  decide (execAttrReplay g wit.ruleSeq wit.wClean = some stmt.claimedAst)

/-- **Honest Completeness (`verifyRewriteAndExtract_complete`)**:
for any LL(1) grammar `g` and safe policy `rules`, sanitizing `wRaw` to `wClean := redactBytes rules wRaw`
and supplying a valid `AttrReplay` certificate `rs` passes `verifyRewriteAndExtract` symbolically
(without unfolding Keccak-f in the kernel). -/
theorem verifyRewriteAndExtract_complete {NT SemOp Val : Type}
    [DecidableEq NT] [DecidableEq SemOp] [DecidableEq Val]
    {g : AttrCfg UInt8 NT SemOp Val} {rules : List (RedactRule UInt8)}
    {wRaw wClean : List UInt8} {rs : List (AttrRule UInt8 NT SemOp)} {ast : Val}
    (hll1 : ll1Deterministic g = true)
    (hsafe : allRulesSafe rules = true)
    (hred : wClean = redactBytes rules wRaw)
    (hrep : AttrReplay g rs wClean ast) :
    verifyRewriteAndExtract g rules (stmtForRewrite wRaw wClean ast) ⟨wRaw, wClean, rs⟩ = true := by
  subst hred
  have hexec : execAttrReplay g rs (redactBytes rules wRaw) = some ast :=
    (execAttrReplay_iff g rs _ ast).mpr hrep
  simp [verifyRewriteAndExtract, stmtForRewrite, hll1, hsafe, hexec]

/-- Helper: equal `(length, contentCommit)` byte records either equal byte-for-byte or expose
an explicit `cSHAKE256` `DenseCollision` (`FramedXofCollision cshakeC`). -/
theorem contentCommit_eq_or_denseCollision {w₁ w₂ : List UInt8}
    (hlen : w₁.length = w₂.length)
    (hroot : contentCommit w₁ = contentCommit w₂) :
    w₁ = w₂ ∨ DenseCollision (w₁.map UInt8.toNat) (w₂.map UInt8.toNat) := by
  rcases denseRoot_eq_or_collision (w₁.map UInt8.toNat) (w₂.map UInt8.toNat)
      (by simp [hlen]) (byte_lt w₁) (byte_lt w₂) hroot with hmap | hcol
  · exact Or.inl (List.map_injective_iff.mpr (fun a b h => UInt8.toNat_inj.mp h) hmap)
  · exact Or.inr hcol

/-- **Capstone Theorem (`rewrite_and_extract_sound_or_collision`):**
Suppose `verifyRewriteAndExtract g rules stmt wit = true`, and `(wRaw, wClean)` are ANY byte records
matching the committed `(rawLength, rawRoot)` and `(cleanLength, cleanRoot)` of `stmt`.
Then EITHER:
1. `wClean = redactBytes rules wRaw` and `RedactsTo rules wRaw wClean` (exact deterministic sanitization),
2. For every rule `rt ∈ rules`, `AbsentPlain wClean rt.pat` AND `wClean` matches `Regex.paddedComplement (Regex.literal rt.pat)`,
3. If `wRaw` was already clean (`∀ r ∈ rules, AbsentPlain wRaw r.pat`), then `wClean = wRaw` (zero mangling),
4. `AttrReplay g wit.ruleSeq wClean stmt.claimedAst` AND `wClean ∈ g.toCfg.language`, AND
5. **Unambiguous AST Extraction:** for EVERY `rs'` and `ast'`,
   `AttrReplay g rs' wClean ast' → ast' = stmt.claimedAst ∧ rs' = wit.ruleSeq` —
OR an explicit `cSHAKE256` `DenseCollision` (`FramedXofCollision cshakeC`) is constructively computed
between the witness tree and the named record tree! -/
theorem rewrite_and_extract_sound_or_collision {NT SemOp Val : Type}
    [DecidableEq NT] [DecidableEq SemOp] [DecidableEq Val]
    (g : AttrCfg UInt8 NT SemOp Val) (rules : List (RedactRule UInt8))
    (stmt : RewriteCertStmt Val) (wit : RewriteCertWitness NT SemOp)
    (hver : verifyRewriteAndExtract g rules stmt wit = true)
    (wRaw wClean : List UInt8) (hcommits : CommitsRewritePair stmt wRaw wClean) :
    (wClean = redactBytes rules wRaw ∧
     RedactsTo rules wRaw wClean ∧
     (∀ rt ∈ rules,
       AbsentPlain wClean rt.pat ∧
       MatchesRegex wClean (Regex.paddedComplement (Regex.literal rt.pat))) ∧
     ((∀ r ∈ rules, AbsentPlain wRaw r.pat) → wClean = wRaw) ∧
     (AttrReplay g wit.ruleSeq wClean stmt.claimedAst ∧ wClean ∈ g.toCfg.language) ∧
     (∀ (rs' : List (AttrRule UInt8 NT SemOp)) (ast' : Val),
       AttrReplay g rs' wClean ast' → ast' = stmt.claimedAst ∧ rs' = wit.ruleSeq)) ∨
    DenseCollision (wit.wRaw.map UInt8.toNat) (wRaw.map UInt8.toNat) ∨
    DenseCollision (wit.wClean.map UInt8.toNat) (wClean.map UInt8.toNat) := by
  unfold verifyRewriteAndExtract at hver
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hver
  rcases hver with ⟨⟨⟨⟨⟨⟨⟨hll1, hsafe⟩, hwRawLen⟩, hwRawRoot⟩, hwCleanLen⟩, hwCleanRoot⟩, hwRed⟩, hwExec⟩
  rcases hcommits with ⟨hnRawLen, hnRawRoot, hnCleanLen, hnCleanRoot⟩
  rcases contentCommit_eq_or_denseCollision
      (hwRawLen.trans hnRawLen.symm) (hwRawRoot.trans hnRawRoot.symm) with hRawEq | hColRaw
  · rcases contentCommit_eq_or_denseCollision
        (hwCleanLen.trans hnCleanLen.symm) (hwCleanRoot.trans hnCleanRoot.symm) with hCleanEq | hColClean
    · left
      subst hRawEq hCleanEq
      have hrep : AttrReplay g wit.ruleSeq wit.wClean stmt.claimedAst :=
        (execAttrReplay_iff g wit.ruleSeq wit.wClean stmt.claimedAst).mp hwExec
      refine ⟨hwRed,
        hwRed ▸ redactsTo_redactBytes rules wit.wRaw,
        fun rt hrt => ?_,
        fun hcl => hwRed.trans (redactBytes_preserves_clean_plain rules wit.wRaw hcl),
        ⟨hrep, attrReplay_mem_language hrep⟩,
        fun rs' ast' hrep' => attrReplay_unique_of_ll1 g hll1 hrep' hrep⟩
      have hsc := redactBytes_scrubs_padded_complement rules hsafe rt hrt wit.wRaw
      rw [← hwRed] at hsc
      exact ⟨hsc.1, hsc.2.1⟩
    · exact Or.inr (Or.inr hColClean)
  · exact Or.inr (Or.inl hColRaw)

/-- **Soundness Tooth 1 (Ambiguous Grammar Refused):**
`verifyRewriteAndExtract` unconditionally rejects `ambigMiniJsonCfg` (`ll1Deterministic = false`),
blocking the duplicate-key splice attack even when commitments and `AttrReplay` succeed. -/
theorem verifyRewriteAndExtract_refuses_ambiguous
    (rules : List (RedactRule UInt8))
    (stmt : RewriteCertStmt MiniValue) (wit : RewriteCertWitness AmbigNT AmbigOp) :
    verifyRewriteAndExtract ambigMiniJsonCfg rules stmt wit = false := by
  have hnot : ll1Deterministic ambigMiniJsonCfg = false := ambigMiniJsonCfg_splice_attack.1
  simp [verifyRewriteAndExtract, hnot]

/-! ## §3. Kernel-Decided (`by decide`) End-to-End Conformance Vectors -/

/-- **Vector 1 (`e2eVec1Raw`):** Agent CoT + tool-call JSON quoting an `sk-proj-...` API key,
a `Bearer` JWT token, and a `{{` template injection inside `"cot"`, plus escaped quotes/backslashes
in `"target"`, sanitized and extracted into a unique `MiniValue.vCotToolCall`. -/
def e2eVec1Raw : List UInt8 :=
  asciiBytes "{\"cot\":\"Found key sk-proj-99aabbcc_1122 and Bearer eyJ0eXAi.payload in {{env}}\",\"tool\":\"backup_snapshot\",\"target\":\"vault\\\\prod\\\"01\",\"amount\":2500}"

def e2eVec1ExpectedClean : List UInt8 :=
  asciiBytes "{\"cot\":\"Found key [REDACTED_API_KEY] and [REDACTED_BEARER] in [REDACTED_TPL]env}}\",\"tool\":\"backup_snapshot\",\"target\":\"vault\\\\prod\\\"01\",\"amount\":2500}"

def e2eVec1ExpectedAst : MiniValue :=
  .vCotToolCall
    (asciiBytes "Found key [REDACTED_API_KEY] and [REDACTED_BEARER] in [REDACTED_TPL]env}}")
    (asciiBytes "backup_snapshot")
    (asciiBytes "vault\\prod\"01")
    2500

def e2eVec1RuleSeq : List (AttrRule UInt8 MiniNT MiniOp) :=
  match ll1Parse miniJsonCfg e2eVec1ExpectedClean with
  | some (rs, _) => rs
  | none => []

set_option maxRecDepth 30000 in
/-- Kernel-decided sanitization + LL(1) AST replay on Vector 1 (`by decide`). -/
theorem e2eVec1_verified :
    redactBytes defaultSecretRules e2eVec1Raw = e2eVec1ExpectedClean ∧
    AttrReplay miniJsonCfg e2eVec1RuleSeq e2eVec1ExpectedClean e2eVec1ExpectedAst ∧
    verifyRewriteAndExtract miniJsonCfg defaultSecretRules
      (stmtForRewrite e2eVec1Raw e2eVec1ExpectedClean e2eVec1ExpectedAst)
      ⟨e2eVec1Raw, e2eVec1ExpectedClean, e2eVec1RuleSeq⟩ = true := by
  have hred : redactBytes defaultSecretRules e2eVec1Raw = e2eVec1ExpectedClean := by decide
  have hrep : AttrReplay miniJsonCfg e2eVec1RuleSeq e2eVec1ExpectedClean e2eVec1ExpectedAst := by
    rw [← execAttrReplay_iff]; decide
  exact ⟨hred, hrep,
    verifyRewriteAndExtract_complete miniJsonCfg_is_ll1 defaultSecretRules_allSafe hred.symm hrep⟩

set_option maxRecDepth 60000 in
/-- **Soundness Tooth 2 (Unredacted Raw CoT Rejected):**
Passing unredacted `e2eVec1Raw` as `wClean` fails `wClean = redactBytes defaultSecretRules wRaw`. -/
theorem e2eVec1_unredacted_rejected (rs : List (AttrRule UInt8 MiniNT MiniOp)) (ast : MiniValue) :
    verifyRewriteAndExtract miniJsonCfg defaultSecretRules
      (stmtForRewrite e2eVec1Raw e2eVec1Raw ast) ⟨e2eVec1Raw, e2eVec1Raw, rs⟩ = false := by
  have hne : e2eVec1Raw ≠ redactBytes defaultSecretRules e2eVec1Raw := by decide
  simp [verifyRewriteAndExtract, hne]

/-- **Soundness Tooth 3 (Forged AST Rejected on Valid Clean Bytes):**
Claiming benign `"read_only"` instead of `"backup_snapshot"` on `e2eVec1ExpectedClean` is rejected
for **every** candidate rule sequence `rs`! -/
def forgedReadOnlyAst : MiniValue :=
  .vCotToolCall
    (asciiBytes "Found key [REDACTED_API_KEY] and [REDACTED_BEARER] in [REDACTED_TPL]env}}")
    (asciiBytes "read_only")
    (asciiBytes "vault\\prod\"01")
    2500

theorem e2eVec1_forged_ast_impossible (rs : List (AttrRule UInt8 MiniNT MiniOp)) :
    ¬ AttrReplay miniJsonCfg rs e2eVec1ExpectedClean forgedReadOnlyAst := by
  intro hforged
  have huniq := (attrReplay_unique_of_ll1 miniJsonCfg miniJsonCfg_is_ll1
    hforged e2eVec1_verified.2.1).1
  exact absurd huniq (by decide)

/-- **Vector 2 (`e2eVec2Raw`):** Clean tool call with escapes (`wClean = wRaw`, zero mangling). -/
def e2eVec2Raw : List UInt8 := sampleEscapedToolJson
def e2eVec2Clean : List UInt8 := sampleEscapedToolJson
def e2eVec2Ast : MiniValue := expectedEscapedToolAst
def e2eVec2RuleSeq : List (AttrRule UInt8 MiniNT MiniOp) := sampleEscapedToolRules

theorem e2eVec2_verified :
    redactBytes defaultSecretRules e2eVec2Raw = e2eVec2Clean ∧
    AttrReplay miniJsonCfg e2eVec2RuleSeq e2eVec2Clean e2eVec2Ast ∧
    verifyRewriteAndExtract miniJsonCfg defaultSecretRules
      (stmtForRewrite e2eVec2Raw e2eVec2Clean e2eVec2Ast)
      ⟨e2eVec2Raw, e2eVec2Clean, e2eVec2RuleSeq⟩ = true := by
  have hred : redactBytes defaultSecretRules e2eVec2Raw = e2eVec2Clean := by decide
  have hrep : AttrReplay miniJsonCfg e2eVec2RuleSeq e2eVec2Clean e2eVec2Ast :=
    miniJsonCfg_extracts_escaped_tool
  exact ⟨hred, hrep,
    verifyRewriteAndExtract_complete miniJsonCfg_is_ll1 defaultSecretRules_allSafe hred.symm hrep⟩

/-- **Vector 3 (`e2eVec3Raw`):** Batch JSON tool-call array containing PEM private key & GitHub PAT in CoT. -/
def e2eVec3Raw : List UInt8 :=
  asciiBytes "[{\"cot\":\"pem=-----BEGIN EC PRIVATE KEY----- pat=ghp_Zz99AaBb_12\",\"tool\":\"rotate_key\",\"target\":\"kms_01\",\"amount\":1}, {\"tool\":\"notify\",\"target\":\"secops\",\"amount\":0}]"

def e2eVec3ExpectedClean : List UInt8 :=
  asciiBytes "[{\"cot\":\"pem=[REDACTED_PEM]pat=[REDACTED_GH_PAT]\",\"tool\":\"rotate_key\",\"target\":\"kms_01\",\"amount\":1}, {\"tool\":\"notify\",\"target\":\"secops\",\"amount\":0}]"

def e2eVec3ExpectedAst : MiniValue :=
  MiniValue.ofBatchList
    [ .vCotToolCall
        (asciiBytes "pem=[REDACTED_PEM]pat=[REDACTED_GH_PAT]")
        (asciiBytes "rotate_key")
        (asciiBytes "kms_01")
        1,
      .vToolCall (asciiBytes "notify") (asciiBytes "secops") 0 ]

def e2eVec3RuleSeq : List (AttrRule UInt8 MiniNT MiniOp) :=
  match ll1Parse miniJsonCfg e2eVec3ExpectedClean with
  | some (rs, _) => rs
  | none => []

set_option maxRecDepth 30000 in
theorem e2eVec3_verified :
    redactBytes defaultSecretRules e2eVec3Raw = e2eVec3ExpectedClean ∧
    AttrReplay miniJsonCfg e2eVec3RuleSeq e2eVec3ExpectedClean e2eVec3ExpectedAst ∧
    verifyRewriteAndExtract miniJsonCfg defaultSecretRules
      (stmtForRewrite e2eVec3Raw e2eVec3ExpectedClean e2eVec3ExpectedAst)
      ⟨e2eVec3Raw, e2eVec3ExpectedClean, e2eVec3RuleSeq⟩ = true := by
  have hred : redactBytes defaultSecretRules e2eVec3Raw = e2eVec3ExpectedClean := by decide
  have hrep : AttrReplay miniJsonCfg e2eVec3RuleSeq e2eVec3ExpectedClean e2eVec3ExpectedAst := by
    rw [← execAttrReplay_iff]; decide
  exact ⟨hred, hrep,
    verifyRewriteAndExtract_complete miniJsonCfg_is_ll1 defaultSecretRules_allSafe hred.symm hrep⟩

/-- Boundary-split & overlapping-prefix redaction stress vector. -/
def boundaryStressRaw : List UInt8 :=
  asciiBytes "chunk_boundary: sk-sk-live_AbCd0123-XyZ! next={{secret}} auth=Bearer a.b.c_d~e+f/g= pem=-----BEGIN OPENSSH PRIVATE KEY----- end"

def boundaryStressExpected : List UInt8 :=
  asciiBytes "chunk_boundary: [REDACTED_API_KEY]! next=[REDACTED_TPL]secret}} auth=[REDACTED_BEARER] pem=[REDACTED_PEM]end"

set_option maxRecDepth 60000 in
theorem boundaryStress_verified :
    redactBytes defaultSecretRules boundaryStressRaw = boundaryStressExpected := by decide

/-! ## §4. Conformance JSON Serializer (`prover/testdata/policy_transducer_conformance.json`) -/

private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (0x30 + n) else Char.ofNat (0x61 + (n - 10))

private def bytesToHex (bs : List UInt8) : String :=
  String.ofList <| bs.flatMap fun b =>
    let v := b.toNat
    [hexDigit (v / 16), hexDigit (v % 16)]

private def digestToHex (d : Digest) : String :=
  bytesToHex (cshakeC.digestCodec.encode d)

private def miniValueToJson : MiniValue → Json
  | .vByte b => Json.mkObj [("kind", "byte"), ("val", toJson b.toNat)]
  | .vBytes bs => Json.mkObj [("kind", "bytes"), ("hex", toJson (bytesToHex bs))]
  | .vDigits ds => Json.mkObj [("kind", "digits"), ("vals", Json.arr (ds.map toJson).toArray)]
  | .vNat n => Json.mkObj [("kind", "nat"), ("val", toJson n)]
  | .vToolCall tool target amount =>
      Json.mkObj
        [ ("kind", "tool_call"),
          ("toolHex", toJson (bytesToHex tool)),
          ("targetHex", toJson (bytesToHex target)),
          ("amount", toJson amount) ]
  | .vCotToolCall cot tool target amount =>
      Json.mkObj
        [ ("kind", "cot_tool_call"),
          ("cotHex", toJson (bytesToHex cot)),
          ("toolHex", toJson (bytesToHex tool)),
          ("targetHex", toJson (bytesToHex target)),
          ("amount", toJson amount) ]
  | .vBatchNil =>
      Json.mkObj [("kind", "batch"), ("items", Json.arr #[])]
  | .vBatchCons hd tl =>
      let rec tailToJson : MiniValue → List Json
        | .vBatchCons x rest => miniValueToJson x :: tailToJson rest
        | _ => []
      Json.mkObj
        [ ("kind", "batch"),
          ("items", Json.arr (miniValueToJson hd :: tailToJson tl).toArray) ]
  | .vUnit => Json.mkObj [("kind", "unit")]

private def ruleIndexIn {T NT SemOp : Type} [DecidableEq T] [DecidableEq NT] [DecidableEq SemOp]
    (rules : List (AttrRule T NT SemOp)) (r : AttrRule T NT SemOp) : Nat :=
  rules.idxOf r

private def e2eVectorJson (name : String) (wRaw wClean : List UInt8)
    (rs : List (AttrRule UInt8 MiniNT MiniOp)) (ast : MiniValue) : Json :=
  Json.mkObj
    [ ("name", toJson name),
      ("rawHex", toJson (bytesToHex wRaw)),
      ("rawLen", toJson wRaw.length),
      ("rawContentRootHex", toJson (digestToHex (contentCommit wRaw))),
      ("cleanHex", toJson (bytesToHex wClean)),
      ("cleanLen", toJson wClean.length),
      ("cleanContentRootHex", toJson (digestToHex (contentCommit wClean))),
      ("ruleIndices", Json.arr (rs.map (fun r => toJson (ruleIndexIn miniJsonCfg.rules r))).toArray),
      ("ast", miniValueToJson ast) ]

private def redactVectorJson (name : String) (wRaw : List UInt8) : Json :=
  let wClean := redactBytes defaultSecretRules wRaw
  Json.mkObj
    [ ("name", toJson name),
      ("rawHex", toJson (bytesToHex wRaw)),
      ("rawLen", toJson wRaw.length),
      ("rawContentRootHex", toJson (digestToHex (contentCommit wRaw))),
      ("cleanHex", toJson (bytesToHex wClean)),
      ("cleanLen", toJson wClean.length),
      ("cleanContentRootHex", toJson (digestToHex (contentCommit wClean))) ]

def policyTransducerConformanceJson : Json :=
  Json.mkObj
    [ ("schema", "minidregg/policy_transducer_conformance/v1"),
      ("ll1Checks", Json.mkObj
        [ ("miniJsonCfgRuleCount", toJson miniJsonCfg.rules.length),
          ("miniJsonCfgDeterministic", toJson (ll1Deterministic miniJsonCfg)),
          ("ambigMiniJsonCfgRuleCount", toJson ambigMiniJsonCfg.rules.length),
          ("ambigMiniJsonCfgDeterministic", toJson (ll1Deterministic ambigMiniJsonCfg)),
          ("defaultSecretRulesSafe", toJson (allRulesSafe defaultSecretRules)) ]),
      ("e2eVectors", Json.arr
        #[ e2eVectorJson "cot_secret_redacted_tool_call"
            e2eVec1Raw e2eVec1ExpectedClean e2eVec1RuleSeq e2eVec1ExpectedAst,
          e2eVectorJson "clean_escaped_tool_call_unmodified"
            e2eVec2Raw e2eVec2Clean e2eVec2RuleSeq e2eVec2Ast,
          e2eVectorJson "batch_tool_calls_pem_and_ghp"
            e2eVec3Raw e2eVec3ExpectedClean e2eVec3RuleSeq e2eVec3ExpectedAst ]),
      ("redactionVectors", Json.arr
        #[ redactVectorJson "dirty_multi_secret_mix" sampleDirtyAgentBytes,
          redactVectorJson "clean_rust_code_preserved" sampleCleanCodeBytes,
          redactVectorJson "boundary_and_overlap_stress" boundaryStressRaw,
          redactVectorJson "overlapping_sk_prefix" (asciiBytes "sk-sk-secret_key_99") ]),
      ("ambigSpliceVector", Json.mkObj
        [ ("payloadHex", toJson (bytesToHex ambigSplicePayload)),
          ("payloadLen", toJson ambigSplicePayload.length),
          ("payloadContentRootHex", toJson (digestToHex (contentCommit ambigSplicePayload))),
          ("benignRuleIndices", Json.arr
            (ambigBenignCert.map (fun r => toJson (ruleIndexIn ambigMiniJsonCfg.rules r))).toArray),
          ("benignAst", miniValueToJson ambigBenignAst),
          ("destructiveRuleIndices", Json.arr
            (ambigDestructiveCert.map (fun r => toJson (ruleIndexIn ambigMiniJsonCfg.rules r))).toArray),
          ("destructiveAst", miniValueToJson ambigDestructiveAst),
          ("ambigGrammarDeterministic", toJson (ll1Deterministic ambigMiniJsonCfg)),
          ("canonicalMiniJsonAccepts", toJson (ll1Parse miniJsonCfg ambigSplicePayload).isSome) ]) ]

/-- Build-time self-test and conformance-vector writer (repo-root-relative). -/
def writePolicyTransducerConformance (path : System.FilePath) : IO Unit := do
  -- Verify runtime cSHAKE256 commitment roots execute cleanly on all three E2E vectors:
  let ok1 := verifyRewriteAndExtract miniJsonCfg defaultSecretRules
    (stmtForRewrite e2eVec1Raw e2eVec1ExpectedClean e2eVec1ExpectedAst)
    ⟨e2eVec1Raw, e2eVec1ExpectedClean, e2eVec1RuleSeq⟩
  let ok2 := verifyRewriteAndExtract miniJsonCfg defaultSecretRules
    (stmtForRewrite e2eVec2Raw e2eVec2Clean e2eVec2Ast)
    ⟨e2eVec2Raw, e2eVec2Clean, e2eVec2RuleSeq⟩
  let ok3 := verifyRewriteAndExtract miniJsonCfg defaultSecretRules
    (stmtForRewrite e2eVec3Raw e2eVec3ExpectedClean e2eVec3ExpectedAst)
    ⟨e2eVec3Raw, e2eVec3ExpectedClean, e2eVec3RuleSeq⟩
  -- Also verify trailing-zero root alias vs length-bound separation on real cSHAKE256:
  let aliasSameRoot := contentCommit (asciiBytes "xab") == contentCommit (asciiBytes "xab" ++ [0])
  unless ok1 && ok2 && ok3 && aliasSameRoot do
    throw (IO.userError "PolicyAstTransducerEmit build-time self-check failed")
  if let some dir := path.parent then IO.FS.createDirAll dir
  IO.FS.writeFile path (policyTransducerConformanceJson.pretty ++ "\n")

#eval writePolicyTransducerConformance "prover/testdata/policy_transducer_conformance.json"

/-! ## §5. Axiom Audit (`#guard_msgs` Pins) -/

/-- info: 'Minidregg.Compiler.PolicyAstTransducerEmit.absentW_iff_padded_complement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms absentW_iff_padded_complement
/-- info: 'Minidregg.Compiler.PolicyAstTransducerEmit.redactBytes_scrubs_padded_complement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms redactBytes_scrubs_padded_complement
/-- info: 'Minidregg.Compiler.PolicyAstTransducerEmit.verifyRewriteAndExtract_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms verifyRewriteAndExtract_complete
/-- info: 'Minidregg.Compiler.PolicyAstTransducerEmit.rewrite_and_extract_sound_or_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rewrite_and_extract_sound_or_collision
/-- info: 'Minidregg.Compiler.PolicyAstTransducerEmit.verifyRewriteAndExtract_refuses_ambiguous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms verifyRewriteAndExtract_refuses_ambiguous
/-- info: 'Minidregg.Compiler.PolicyAstTransducerEmit.e2eVec1_verified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms e2eVec1_verified
/-- info: 'Minidregg.Compiler.PolicyAstTransducerEmit.e2eVec1_forged_ast_impossible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms e2eVec1_forged_ast_impossible
/-- info: 'Minidregg.Compiler.PolicyAstTransducerEmit.e2eVec3_verified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms e2eVec3_verified

end Minidregg.Compiler.PolicyAstTransducerEmit
