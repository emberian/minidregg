/-
# `Assurance/VerifiableAgentTurnWeld.lean` — End-to-End Byte-Stream Turn Weld (`U1` + `RewriteCert` + LL(1) `CotToolCall`)

Closes the **#5 Trust-Boundary Gap** between:
1. **`U1` Model-Audit Boundary Commitments (`Produced`, `P8`):** SP 800-185 `cSHAKE256` hash-chain
   from `(weightRoot, promptLength, promptRoot)` across all `L + 1` layer boundaries `B_0 .. B_L`,
   Fiat–Shamir VRF layer selection (`u1VrfSelectLayer`), and `u1ProofDigest` to `(rawLength, rawRoot)`,
2. **Canonical Multi-Pattern Secret Sanitization (`RewriteCert`):** deterministic byte transducer
   `wClean = redactBytes defaultSecretRules wRaw` with universal `AbsentPlain` and Brzozowski
   `Regex.paddedComplement` guarantees across all 5 secret classes (`sk-`, `Bearer `, `-----BEGIN `,
   `{{`, `ghp_`), and
3. **Unambiguous LL(1) AST Extraction (`miniJsonCfg`, `CotToolCall`):** linear-time attributed
   replay over the 139-rule deterministic `miniJsonCfg` grammar guaranteeing at most one AST per
   sanitized transcript (`∀ rs' ast', AttrReplay miniJsonCfg rs' wClean ast' → ast' = stmt.claimedAst`),
all parsed directly from prefix-free canonical `StreamCodec` wire bytes (`VASTMT01` / `VAGENT01`)
shared byte-for-byte with the native Rust exact-integer `Qwen3.5-0.8B` agent runner!

## Core Results (`0 sorry`, `0` custom `axiom`, `0 native_decide`, `0 #guard`)

- **`decodeTurnStmt_encodeTurnStmt`, `encodeTurnStmt_injective`, `trailing_stmt_bytes_refused`,
  `decodeTurnReceipt_encodeTurnReceipt`, `encodeTurnReceipt_injective`, `trailing_wire_bytes_refused`:**
  Canonical `StreamCodec` round-trip, injectivity, and trailing-byte refusal on `VASTMT01` & `VAGENT01`.
- **`u1TurnHead_eq_or_collision` (`U1TurnHeadCollision`):**
  Full inductive `cSHAKE256` hash-chain collision extraction with deterministic input-pinned `Frames`
  (`u1TurnHeadCollisionFrames` — never an existential over the suite): two boundary chains producing
  the same 32-byte `turnChainRoot` agree on `weightRoot`, `promptLength`, `promptRoot`, every
  intermediate layer boundary `boundaryRoots[0 .. L]`, `u1ProofDigest`, `rawLength`, and `rawRoot` —
  or collide at the exact computed `Frames`.
- **`verifyAgentTurnBytes_sound_or_collision` (`AgentTurnWeldCollision`):**
  End-to-end byte-verifier soundness welding canonical wire decoding, `U1` boundary-chain commitment,
  `wClean = redactBytes defaultSecretRules wRaw` + universal `Regex.paddedComplement` secret absence,
  and unique LL(1) `MiniValue` AST + rule-sequence extraction, up to input-pinned `AgentTurnWeldCollision`.
- **`verifyAgentTurnBytes_certSound` & `verifiableAgentTurn_produced_weld`:**
  Concrete `CertSound` discharge of `verifyAgentTurnBytes` over `lengthRootScheme` (`ε_cert = 0`,
  non-trivial `CertifiedSanitizedTurn` with `certifiedSanitizedTurn_empty_false`) welded directly to
  any `U1` model-production verifier `V_u1` via `CertificateComposition.cert_produced_weld` (`P8`).
- **Premise inhabitation, concrete & universal `TK` prompt/boundary mismatch falsifiers, universal
  `dirty_clean_bytes_refused` (`¬ AbsentPlain`), universal `duplicate_key_splice_refused` on
  `ambigSplicePayload`, and `#eval` cross-verification on live 24-layer `Qwen3.5-0.8B` `VASTMT01`
  (`236 B`) & `VAGENT01` (`1,415 B`) wire bytes.**
-/

import Theory.StreamCodec
import Theory.VerifiedAstTransducer
import Selvage.ContentCertificate
import Compiler.Sp800185Cshake256
import Compiler.Tower256ContentCert
import Compiler.Tower256PrivateContentCert
import Compiler.PolicyAstTransducerEmit
import Assurance.CertificateComposition

namespace Minidregg.Assurance.VerifiableAgentTurnWeld

open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization (Digest)
open Minidregg.Theory.VerifiedAstTransducer
open Minidregg.Selvage
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.Tower256CshakeMerkleController (Cshake256 MerkleDomains cubeRoot)
open Minidregg.Compiler.Tower256CshakeMerkleBinding (FramedXofCollision)
open Minidregg.Compiler.Tower256CoordinateMerkle (cshakeC merkleDomainsC codecC)
open Minidregg.Compiler.Tower256ContentCert (contentCommit DenseCollision Frames)
open Minidregg.Compiler.PolicyAstTransducerEmit
  (contentCommit_eq_or_denseCollision redactBytes_scrubs_padded_complement
   redactBytes_preserves_clean_plain)
open Minidregg.Assurance.CertificateComposition

set_option autoImplicit false

/-! ## §1. Canonical Prefix-Free `StreamCodec` for `MiniValue` -/

/-- Prefix-free wire encoder for `MiniValue` matching `qwen35audit::agent_runner::stream_encode_mini_value`. -/
def encodeMiniValue : MiniValue → List UInt8
  | .vByte b => 0 :: [b]
  | .vBytes bs => 1 :: bytesStream.encode bs
  | .vDigits ds => 2 :: (StreamCodec.list StreamCodec.nat).encode ds
  | .vNat n => 3 :: StreamCodec.nat.encode n
  | .vToolCall tool target amount =>
      4 :: (bytesStream.encode tool ++ bytesStream.encode target ++ StreamCodec.nat.encode amount)
  | .vCotToolCall cot tool target amount =>
      5 :: (bytesStream.encode cot ++ bytesStream.encode tool ++
            bytesStream.encode target ++ StreamCodec.nat.encode amount)
  | .vBatchNil => [6]
  | .vBatchCons hd tl => 7 :: (encodeMiniValue hd ++ encodeMiniValue tl)
  | .vUnit => [8]

theorem encodeMiniValue_pos : ∀ v : MiniValue, 0 < (encodeMiniValue v).length
  | .vByte _ | .vBytes _ | .vDigits _ | .vNat _ | .vToolCall _ _ _
  | .vCotToolCall _ _ _ _ | .vBatchNil | .vBatchCons _ _ | .vUnit => by
      simp [encodeMiniValue]

/-- Fuel-bounded prefix decoder for `MiniValue`; `fuel = bytes.length` suffices for every valid wire. -/
def decodeMiniValueFuel : Nat → List UInt8 → Option (MiniValue × List UInt8)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, tag :: rest =>
      if tag = 0 then
        match rest with
        | [] => none
        | b :: sfx => some (.vByte b, sfx)
      else if tag = 1 then do
        let (bs, sfx) ← bytesStream.decodePrefix rest
        some (.vBytes bs, sfx)
      else if tag = 2 then do
        let (ds, sfx) ← (StreamCodec.list StreamCodec.nat).decodePrefix rest
        some (.vDigits ds, sfx)
      else if tag = 3 then do
        let (n, sfx) ← StreamCodec.nat.decodePrefix rest
        some (.vNat n, sfx)
      else if tag = 4 then do
        let (tool, r1) ← bytesStream.decodePrefix rest
        let (target, r2) ← bytesStream.decodePrefix r1
        let (amount, sfx) ← StreamCodec.nat.decodePrefix r2
        some (.vToolCall tool target amount, sfx)
      else if tag = 5 then do
        let (cot, r1) ← bytesStream.decodePrefix rest
        let (tool, r2) ← bytesStream.decodePrefix r1
        let (target, r3) ← bytesStream.decodePrefix r2
        let (amount, sfx) ← StreamCodec.nat.decodePrefix r3
        some (.vCotToolCall cot tool target amount, sfx)
      else if tag = 6 then
        some (.vBatchNil, rest)
      else if tag = 7 then do
        let (hd, r1) ← decodeMiniValueFuel fuel rest
        let (tl, sfx) ← decodeMiniValueFuel fuel r1
        some (.vBatchCons hd tl, sfx)
      else if tag = 8 then
        some (.vUnit, rest)
      else
        none

def decodeMiniValuePrefix (bytes : List UInt8) : Option (MiniValue × List UInt8) :=
  decodeMiniValueFuel bytes.length bytes

theorem decodeMiniValueFuel_encode :
    ∀ (v : MiniValue) (fuel : Nat) (suffix : List UInt8),
      (encodeMiniValue v).length ≤ fuel →
      decodeMiniValueFuel fuel (encodeMiniValue v ++ suffix) = some (v, suffix) := by
  intro v
  induction v with
  | vByte b =>
      intro fuel suffix hlen
      cases fuel with
      | zero => have := encodeMiniValue_pos (.vByte b); omega
      | succ fuel => simp [encodeMiniValue, decodeMiniValueFuel]
  | vBytes bs =>
      intro fuel suffix hlen
      cases fuel with
      | zero => have := encodeMiniValue_pos (.vBytes bs); omega
      | succ fuel =>
          simp [encodeMiniValue, decodeMiniValueFuel, bytesStream.decodePrefix_encode]
  | vDigits ds =>
      intro fuel suffix hlen
      cases fuel with
      | zero => have := encodeMiniValue_pos (.vDigits ds); omega
      | succ fuel =>
          simp [encodeMiniValue, decodeMiniValueFuel,
            (StreamCodec.list StreamCodec.nat).decodePrefix_encode]
  | vNat n =>
      intro fuel suffix hlen
      cases fuel with
      | zero => have := encodeMiniValue_pos (.vNat n); omega
      | succ fuel =>
          simp [encodeMiniValue, decodeMiniValueFuel, StreamCodec.nat.decodePrefix_encode]
  | vToolCall tool target amount =>
      intro fuel suffix hlen
      cases fuel with
      | zero => have := encodeMiniValue_pos (.vToolCall tool target amount); omega
      | succ fuel =>
          have htag4 : (4 : UInt8) ≠ 0 ∧ (4 : UInt8) ≠ 1 ∧ (4 : UInt8) ≠ 2 ∧ (4 : UInt8) ≠ 3 := by
            decide
          simp [encodeMiniValue, decodeMiniValueFuel, htag4, List.append_assoc,
            bytesStream.decodePrefix_encode, StreamCodec.nat.decodePrefix_encode]
  | vCotToolCall cot tool target amount =>
      intro fuel suffix hlen
      cases fuel with
      | zero => have := encodeMiniValue_pos (.vCotToolCall cot tool target amount); omega
      | succ fuel =>
          have htag5 : (5 : UInt8) ≠ 0 ∧ (5 : UInt8) ≠ 1 ∧ (5 : UInt8) ≠ 2 ∧
              (5 : UInt8) ≠ 3 ∧ (5 : UInt8) ≠ 4 := by decide
          simp [encodeMiniValue, decodeMiniValueFuel, htag5, List.append_assoc,
            bytesStream.decodePrefix_encode, StreamCodec.nat.decodePrefix_encode]
  | vBatchNil =>
      intro fuel suffix hlen
      cases fuel with
      | zero => have := encodeMiniValue_pos .vBatchNil; omega
      | succ fuel =>
          have htag6 : (6 : UInt8) ≠ 0 ∧ (6 : UInt8) ≠ 1 ∧ (6 : UInt8) ≠ 2 ∧
              (6 : UInt8) ≠ 3 ∧ (6 : UInt8) ≠ 4 ∧ (6 : UInt8) ≠ 5 := by decide
          simp [encodeMiniValue, decodeMiniValueFuel, htag6]
  | vBatchCons hd tl ihHd ihTl =>
      intro fuel suffix hlen
      cases fuel with
      | zero => have := encodeMiniValue_pos (.vBatchCons hd tl); omega
      | succ fuel =>
          simp only [encodeMiniValue, List.length_cons, List.length_append] at hlen
          have hhd := ihHd fuel (encodeMiniValue tl ++ suffix) (by omega)
          have htl := ihTl fuel suffix (by omega)
          have htag7 : (7 : UInt8) ≠ 0 ∧ (7 : UInt8) ≠ 1 ∧ (7 : UInt8) ≠ 2 ∧
              (7 : UInt8) ≠ 3 ∧ (7 : UInt8) ≠ 4 ∧ (7 : UInt8) ≠ 5 ∧ (7 : UInt8) ≠ 6 := by decide
          simp [encodeMiniValue, decodeMiniValueFuel, htag7, List.append_assoc, hhd, htl]
  | vUnit =>
      intro fuel suffix hlen
      cases fuel with
      | zero => have := encodeMiniValue_pos .vUnit; omega
      | succ fuel =>
          have htag8 : (8 : UInt8) ≠ 0 ∧ (8 : UInt8) ≠ 1 ∧ (8 : UInt8) ≠ 2 ∧
              (8 : UInt8) ≠ 3 ∧ (8 : UInt8) ≠ 4 ∧ (8 : UInt8) ≠ 5 ∧
              (8 : UInt8) ≠ 6 ∧ (8 : UInt8) ≠ 7 := by decide
          simp [encodeMiniValue, decodeMiniValueFuel, htag8]

theorem encode_decodeMiniValueFuel :
    ∀ (fuel : Nat) (bytes : List UInt8) (v : MiniValue) (suffix : List UInt8),
      decodeMiniValueFuel fuel bytes = some (v, suffix) →
      encodeMiniValue v ++ suffix = bytes := by
  intro fuel
  induction fuel with
  | zero =>
      intro bytes v suffix h
      cases h
  | succ fuel ih =>
      intro bytes v suffix h
      rcases bytes with _ | ⟨tag, rest⟩
      · simp [decodeMiniValueFuel] at h
      · simp only [decodeMiniValueFuel] at h
        by_cases h0 : tag = 0
        · subst h0
          simp only [↓reduceIte] at h
          rcases rest with _ | ⟨b, sfx⟩
          · cases h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, rfl⟩
            rfl
        · simp only [h0, ↓reduceIte] at h
          by_cases h1 : tag = 1
          · subst h1
            simp only [↓reduceIte, bind, Option.bind] at h
            cases hdec : bytesStream.decodePrefix rest with
            | none => simp [hdec] at h
            | some pair =>
                rcases pair with ⟨bs, sfx⟩
                simp only [hdec, Option.some.injEq, Prod.mk.injEq] at h
                rcases h with ⟨rfl, rfl⟩
                simp [encodeMiniValue, bytesStream.encode_decodePrefix _ _ _ hdec]
          · simp only [h1, ↓reduceIte] at h
            by_cases h2 : tag = 2
            · subst h2
              simp only [↓reduceIte, bind, Option.bind] at h
              cases hdec : (StreamCodec.list StreamCodec.nat).decodePrefix rest with
              | none => simp [hdec] at h
              | some pair =>
                  rcases pair with ⟨ds, sfx⟩
                  simp only [hdec, Option.some.injEq, Prod.mk.injEq] at h
                  rcases h with ⟨rfl, rfl⟩
                  simp [encodeMiniValue,
                    (StreamCodec.list StreamCodec.nat).encode_decodePrefix _ _ _ hdec]
            · simp only [h2, ↓reduceIte] at h
              by_cases h3 : tag = 3
              · subst h3
                simp only [↓reduceIte, bind, Option.bind] at h
                cases hdec : StreamCodec.nat.decodePrefix rest with
                | none => simp [hdec] at h
                | some pair =>
                    rcases pair with ⟨n, sfx⟩
                    simp only [hdec, Option.some.injEq, Prod.mk.injEq] at h
                    rcases h with ⟨rfl, rfl⟩
                    simp [encodeMiniValue, StreamCodec.nat.encode_decodePrefix _ _ _ hdec]
              · simp only [h3, ↓reduceIte] at h
                by_cases h4 : tag = 4
                · subst h4
                  simp only [↓reduceIte, Option.bind_eq_bind, Option.bind_eq_some_iff,
                    Prod.exists] at h
                  rcases h with ⟨tool, r1, ht, target, r2, htg, amount, sfx, ha, hs⟩
                  simp only [Option.some.injEq, Prod.mk.injEq] at hs
                  rcases hs with ⟨rfl, rfl⟩
                  have e1 := bytesStream.encode_decodePrefix _ _ _ ht
                  have e2 := bytesStream.encode_decodePrefix _ _ _ htg
                  have e3 := StreamCodec.nat.encode_decodePrefix _ _ _ ha
                  simp [encodeMiniValue, List.append_assoc, e3, e2, e1]
                · simp only [h4, ↓reduceIte] at h
                  by_cases h5 : tag = 5
                  · subst h5
                    simp only [↓reduceIte, Option.bind_eq_bind, Option.bind_eq_some_iff,
                      Prod.exists] at h
                    rcases h with ⟨cot, r1, hc, tool, r2, ht, target, r3, htg, amount, sfx, ha, hs⟩
                    simp only [Option.some.injEq, Prod.mk.injEq] at hs
                    rcases hs with ⟨rfl, rfl⟩
                    have e0 := bytesStream.encode_decodePrefix _ _ _ hc
                    have e1 := bytesStream.encode_decodePrefix _ _ _ ht
                    have e2 := bytesStream.encode_decodePrefix _ _ _ htg
                    have e3 := StreamCodec.nat.encode_decodePrefix _ _ _ ha
                    simp [encodeMiniValue, List.append_assoc, e3, e2, e1, e0]
                  · simp only [h5, ↓reduceIte] at h
                    by_cases h6 : tag = 6
                    · subst h6
                      simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
                      rcases h with ⟨rfl, rfl⟩
                      rfl
                    · simp only [h6, ↓reduceIte] at h
                      by_cases h7 : tag = 7
                      · subst h7
                        simp only [↓reduceIte, Option.bind_eq_bind, Option.bind_eq_some_iff,
                          Prod.exists] at h
                        rcases h with ⟨hd, r1, hhd, tl, sfx, htl, hs⟩
                        simp only [Option.some.injEq, Prod.mk.injEq] at hs
                        rcases hs with ⟨rfl, rfl⟩
                        have ehd := ih rest hd r1 hhd
                        have etl := ih r1 tl sfx htl
                        simp only [encodeMiniValue, List.cons_append, List.append_assoc,
                          List.cons.injEq, true_and]
                        rw [etl]
                        exact ehd
                      · simp only [h7, ↓reduceIte] at h
                        by_cases h8 : tag = 8
                        · subst h8
                          simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
                          rcases h with ⟨rfl, rfl⟩
                          rfl
                        · simp [h8] at h

/-- Lawful canonical `StreamCodec` for `MiniValue`. -/
def miniValueStream : StreamCodec MiniValue where
  encode := encodeMiniValue
  decodePrefix := decodeMiniValuePrefix
  decodePrefix_encode := by
    intro v suffix
    unfold decodeMiniValuePrefix
    exact decodeMiniValueFuel_encode v _ suffix (by simp)
  encode_decodePrefix := by
    intro bytes v suffix h
    exact encode_decodeMiniValueFuel bytes.length bytes v suffix h

/-! ## §2. `VerifiableAgentTurnStmt` (`VASTMT01`) & `VerifiableAgentTurnReceipt` (`VAGENT01`) Wire Codecs -/

/-- Public end-to-end turn statement (`VASTMT01` wire frame). -/
structure VerifiableAgentTurnStmt where
  weightRoot    : Digest256
  promptLength  : Nat
  promptRoot    : Digest256
  numLayers     : Nat
  turnChainRoot : Digest256
  rawLength     : Nat
  rawRoot       : Digest256
  cleanLength   : Nat
  cleanRoot     : Digest256
  claimedAst    : MiniValue
  deriving DecidableEq, Repr

/-- End-to-end turn receipt (`VAGENT01` wire frame). -/
structure VerifiableAgentTurnReceipt where
  promptBytes     : List UInt8
  boundaryRoots   : List Digest256
  auditedLayer    : Nat
  auditedBInRoot  : Digest256
  auditedBOutRoot : Digest256
  u1ProofDigest   : Digest256
  wRaw            : List UInt8
  wClean          : List UInt8
  ruleIndices     : List Nat
  deriving DecidableEq, Repr

def vastmt01Magic : List UInt8 := asciiBytes "VASTMT01"
def vagent01Magic : List UInt8 := asciiBytes "VAGENT01"

abbrev TurnStmtWire :=
  Digest256 × Nat × Digest256 × Nat × Digest256 × Nat × Digest256 × Nat × Digest256 × MiniValue

def turnStmtWireStream : StreamCodec TurnStmtWire :=
  StreamCodec.product digest256Stream
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product digest256Stream
        (StreamCodec.product StreamCodec.nat
          (StreamCodec.product digest256Stream
            (StreamCodec.product StreamCodec.nat
              (StreamCodec.product digest256Stream
                (StreamCodec.product StreamCodec.nat
                  (StreamCodec.product digest256Stream miniValueStream))))))))

/-- Canonical `VASTMT01` `StreamCodec` for `VerifiableAgentTurnStmt`. -/
def turnStmtStream : StreamCodec VerifiableAgentTurnStmt :=
  StreamCodec.framed vastmt01Magic
    (StreamCodec.xmap turnStmtWireStream
      (fun s => (s.weightRoot, s.promptLength, s.promptRoot, s.numLayers, s.turnChainRoot,
        s.rawLength, s.rawRoot, s.cleanLength, s.cleanRoot, s.claimedAst))
      (fun (wR, pL, pR, nL, tR, rL, rR, cL, cR, ast) =>
        ⟨wR, pL, pR, nL, tR, rL, rR, cL, cR, ast⟩)
      (by intro s; cases s; rfl))

abbrev TurnReceiptWire :=
  List UInt8 × List Digest256 × Nat × Digest256 × Digest256 × Digest256 ×
    List UInt8 × List UInt8 × List Nat

def turnReceiptWireStream : StreamCodec TurnReceiptWire :=
  StreamCodec.product bytesStream
    (StreamCodec.product (StreamCodec.list digest256Stream)
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product digest256Stream
          (StreamCodec.product digest256Stream
            (StreamCodec.product digest256Stream
              (StreamCodec.product bytesStream
                (StreamCodec.product bytesStream
                  (StreamCodec.list StreamCodec.nat))))))))

/-- Canonical `VAGENT01` `StreamCodec` for `VerifiableAgentTurnReceipt`. -/
def turnReceiptStream : StreamCodec VerifiableAgentTurnReceipt :=
  StreamCodec.framed vagent01Magic
    (StreamCodec.xmap turnReceiptWireStream
      (fun r => (r.promptBytes, r.boundaryRoots, r.auditedLayer, r.auditedBInRoot,
        r.auditedBOutRoot, r.u1ProofDigest, r.wRaw, r.wClean, r.ruleIndices))
      (fun (pB, bRs, aL, bIn, bOut, pfD, wR, wC, rI) =>
        ⟨pB, bRs, aL, bIn, bOut, pfD, wR, wC, rI⟩)
      (by intro r; cases r; rfl))

def encodeTurnStmt (s : VerifiableAgentTurnStmt) : List UInt8 :=
  turnStmtStream.encode s

def decodeTurnStmt (bytes : List UInt8) : Option VerifiableAgentTurnStmt :=
  turnStmtStream.toLawful.decode bytes

def encodeTurnReceipt (r : VerifiableAgentTurnReceipt) : List UInt8 :=
  turnReceiptStream.encode r

def decodeTurnReceipt (bytes : List UInt8) : Option VerifiableAgentTurnReceipt :=
  turnReceiptStream.toLawful.decode bytes

theorem decodeTurnStmt_encodeTurnStmt (s : VerifiableAgentTurnStmt) :
    decodeTurnStmt (encodeTurnStmt s) = some s :=
  turnStmtStream.toLawful.decode_encode s

theorem decodeTurnStmt_eq_some_iff (bytes : List UInt8) (s : VerifiableAgentTurnStmt) :
    decodeTurnStmt bytes = some s ↔ encodeTurnStmt s = bytes :=
  turnStmtStream.toLawful_decode_iff bytes s

theorem encodeTurnStmt_injective : Function.Injective encodeTurnStmt := by
  intro s₁ s₂ heq
  have h := congrArg decodeTurnStmt heq
  rwa [decodeTurnStmt_encodeTurnStmt, decodeTurnStmt_encodeTurnStmt, Option.some.injEq] at h

theorem decodeTurnReceipt_encodeTurnReceipt (r : VerifiableAgentTurnReceipt) :
    decodeTurnReceipt (encodeTurnReceipt r) = some r :=
  turnReceiptStream.toLawful.decode_encode r

theorem decodeTurnReceipt_eq_some_iff (bytes : List UInt8) (r : VerifiableAgentTurnReceipt) :
    decodeTurnReceipt bytes = some r ↔ encodeTurnReceipt r = bytes :=
  turnReceiptStream.toLawful_decode_iff bytes r

theorem encodeTurnReceipt_injective : Function.Injective encodeTurnReceipt := by
  intro r₁ r₂ heq
  have h := congrArg decodeTurnReceipt heq
  rwa [decodeTurnReceipt_encodeTurnReceipt, decodeTurnReceipt_encodeTurnReceipt, Option.some.injEq] at h

/-- Appending any non-empty trailing byte suffix to a `VASTMT01` statement is strictly refused. -/
theorem trailing_stmt_bytes_refused (s : VerifiableAgentTurnStmt) (extra : List UInt8)
    (hne : extra ≠ []) :
    decodeTurnStmt (encodeTurnStmt s ++ extra) = none := by
  cases hdec : decodeTurnStmt (encodeTurnStmt s ++ extra) with
  | none => rfl
  | some s' =>
      have henc := (decodeTurnStmt_eq_some_iff _ s').mp hdec
      have h1 := turnStmtStream.decodePrefix_encode s' []
      have h2 : turnStmtStream.encode s' = turnStmtStream.encode s ++ extra := henc
      rw [List.append_nil, h2, turnStmtStream.decodePrefix_encode s extra] at h1
      simp [hne] at h1

/-- Appending any non-empty trailing byte suffix to a `VAGENT01` receipt is strictly refused. -/
theorem trailing_wire_bytes_refused (r : VerifiableAgentTurnReceipt) (extra : List UInt8)
    (hne : extra ≠ []) :
    decodeTurnReceipt (encodeTurnReceipt r ++ extra) = none := by
  cases hdec : decodeTurnReceipt (encodeTurnReceipt r ++ extra) with
  | none => rfl
  | some r' =>
      have henc := (decodeTurnReceipt_eq_some_iff _ r').mp hdec
      have h1 := turnReceiptStream.decodePrefix_encode r' []
      have h2 : turnReceiptStream.encode r' = turnReceiptStream.encode r ++ extra := henc
      rw [List.append_nil, h2, turnReceiptStream.decodePrefix_encode r extra] at h1
      simp [hne] at h1

/-! ## §3. `U1` Boundary Hash Chain, Fiat–Shamir VRF Layer Selection, & Chain Collision Extraction -/

def u1StepCustomization : List UInt8 :=
  0x07 :: asciiBytes "MINIDREGG/VAGENT01/U1/CHAIN/STEP/V1"

def u1OutCustomization : List UInt8 :=
  0x08 :: asciiBytes "MINIDREGG/VAGENT01/U1/OUT/WELD/V1"

def u1VrfCustomization : List UInt8 :=
  0x09 :: asciiBytes "MINIDREGG/VAGENT01/U1/VRF/SELECT/V1"

/-- Project a concrete `cshakeC` 32-byte XOF digest into `Digest256` without truncation. -/
def cshake256D256 (customization input : List UInt8) : Digest256 :=
  toDigest256 (cshakeC.xofDigest customization input)
    (Minidregg.Compiler.Sp800185Cshake256.hash_digest_lt customization input)

theorem ofDigest256_cshake256D256 (customization input : List UInt8) :
    ofDigest256 (cshake256D256 customization input) = cshakeC.xofDigest customization input :=
  ofDigest256_toDigest256 _ _

theorem cubeRootC_lt {R : Type} (codec : LawfulCodec R) :
    ∀ {k : Nat} (col : (Fin k → Bool) → R), (cubeRoot merkleDomainsC codec col).value < 256 ^ 32
  | 0, _ => Minidregg.Compiler.Sp800185Cshake256.hash_digest_lt _ _
  | _ + 1, _ => Minidregg.Compiler.Sp800185Cshake256.hash_digest_lt _ _

theorem contentCommit_lt (w : List UInt8) : (contentCommit w).value < 256 ^ 32 :=
  cubeRootC_lt codecC _

/-- Total `Digest256` projection of `contentCommit w`. -/
def contentCommit256 (w : List UInt8) : Digest256 :=
  toDigest256 (contentCommit w) (contentCommit_lt w)

@[simp] theorem ofDigest256_contentCommit256 (w : List UInt8) :
    ofDigest256 (contentCommit256 w) = contentCommit w :=
  ofDigest256_toDigest256 _ _

theorem streamCodec_encode_injective {α : Type} (codec : StreamCodec α) :
    Function.Injective codec.encode := by
  intro a b heq
  have h := congrArg codec.toLawful.decode heq
  exact Option.some.inj ((codec.toLawful.decode_encode a).symm.trans (h.trans (codec.toLawful.decode_encode b)))

theorem cshake256D256_eq_or_collision (cust inp₁ inp₂ : List UInt8)
    (heq : cshake256D256 cust inp₁ = cshake256D256 cust inp₂) :
    inp₁ = inp₂ ∨ FramedXofCollision cshakeC cust inp₁ inp₂ := by
  by_cases hinp : inp₁ = inp₂
  · exact Or.inl hinp
  · right
    have hd : cshakeC.xofDigest cust inp₁ = cshakeC.xofDigest cust inp₂ := by
      rw [← ofDigest256_cshake256D256, ← ofDigest256_cshake256D256, heq]
    exact ⟨hinp, hd⟩

def u1StepFrameCodec : StreamCodec (Nat × Digest256 × Nat × Digest256) :=
  StreamCodec.product StreamCodec.nat
    (StreamCodec.product digest256Stream
      (StreamCodec.product StreamCodec.nat digest256Stream))

def u1OutFrameCodec : StreamCodec (Digest256 × Nat × Digest256 × Nat × Digest256) :=
  StreamCodec.product digest256Stream
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product digest256Stream
        (StreamCodec.product StreamCodec.nat digest256Stream)))

def u1VrfFrameCodec : StreamCodec (Digest256 × List Digest256 × Digest256 × Nat) :=
  StreamCodec.product digest256Stream
    (StreamCodec.product (StreamCodec.list digest256Stream)
      (StreamCodec.product digest256Stream StreamCodec.nat))

def u1InitAcc (weightRoot promptRoot : Digest256) (promptLen : Nat) : Digest256 :=
  cshake256D256 u1StepCustomization
    (u1StepFrameCodec.encode (0, weightRoot, promptLen, promptRoot))

def u1StepAcc (acc : Digest256) (idx : Nat) (bRoot : Digest256) : Digest256 :=
  cshake256D256 u1StepCustomization
    (u1StepFrameCodec.encode (1, acc, idx, bRoot))

def u1StepLoop : Nat → Digest256 → List Digest256 → Digest256
  | _, acc, [] => acc
  | idx, acc, bRoot :: rest => u1StepLoop (idx + 1) (u1StepAcc acc idx bRoot) rest

def u1ChainFold (weightRoot promptRoot : Digest256) (promptLen : Nat)
    (boundaryRoots : List Digest256) : Digest256 :=
  u1StepLoop 0 (u1InitAcc weightRoot promptRoot promptLen) boundaryRoots

def u1TurnHead (weightRoot promptRoot : Digest256) (promptLen : Nat)
    (boundaryRoots : List Digest256) (u1ProofDigest : Digest256)
    (rawLen : Nat) (rawRoot : Digest256) : Digest256 :=
  cshake256D256 u1OutCustomization
    (u1OutFrameCodec.encode
      (u1ChainFold weightRoot promptRoot promptLen boundaryRoots,
       boundaryRoots.length, u1ProofDigest, rawLen, rawRoot))

/-- The 18 `GDN` (`GatedDeltaNet + SwiGLU`) layer indices of `Qwen3.5-0.8B` (`l % 4 != 3`). -/
def qwen35GdnLayers : List Nat :=
  [0, 1, 2, 4, 5, 6, 8, 9, 10, 12, 13, 14, 16, 17, 18, 20, 21, 22]

/-- Deterministic Fiat–Shamir VRF layer selector matching `compute_u1_vrf_layer_cshake` in Rust. -/
def u1VrfSelectLayer (weightRoot : Digest256) (boundaryRoots : List Digest256)
    (cleanRoot : Digest256) (numLayers : Nat) : Nat :=
  let frame := u1VrfFrameCodec.encode (weightRoot, boundaryRoots, cleanRoot, numLayers)
  let vrfDig := cshake256D256 u1VrfCustomization frame
  let low32 := vrfDig.val % (256 ^ 4)
  if numLayers = 24 then
    qwen35GdnLayers.getD (low32 % 18) 0
  else if numLayers = 0 then
    0
  else
    low32 % numLayers

theorem qwen35GdnLayers_getD_lt_24 (k : Nat) (hk : k < 18) :
    qwen35GdnLayers.getD k 0 < 24 := by
  have hmem : ∀ i ∈ List.range 18, qwen35GdnLayers.getD i 0 < 24 := by decide
  exact hmem k (List.mem_range.mpr hk)

theorem u1VrfSelectLayer_lt (weightRoot : Digest256) (boundaryRoots : List Digest256)
    (cleanRoot : Digest256) {numLayers : Nat} (hpos : 0 < numLayers) :
    u1VrfSelectLayer weightRoot boundaryRoots cleanRoot numLayers < numLayers := by
  unfold u1VrfSelectLayer
  dsimp only
  split
  · rename_i h24
    subst h24
    exact qwen35GdnLayers_getD_lt_24 _ (Nat.mod_lt _ (by decide))
  · rename_i hne24
    have hne0 : numLayers ≠ 0 := by omega
    simp [hne0, Nat.mod_lt _ hpos]

theorem u1StepLoop_append_singleton (idx : Nat) (acc : Digest256)
    (bs : List Digest256) (bLast : Digest256) :
    u1StepLoop idx acc (bs ++ [bLast]) =
      u1StepAcc (u1StepLoop idx acc bs) (idx + bs.length) bLast := by
  induction bs generalizing idx acc with
  | nil => simp [u1StepLoop]
  | cons b bs ih =>
      simp only [List.cons_append, u1StepLoop, ih, List.length_cons]
      have hadd : idx + 1 + bs.length = idx + (bs.length + 1) := by omega
      rw [hadd]

theorem u1ChainFold_append_singleton (w p : Digest256) (pl : Nat)
    (bs : List Digest256) (bLast : Digest256) :
    u1ChainFold w p pl (bs ++ [bLast]) = u1StepAcc (u1ChainFold w p pl bs) bs.length bLast := by
  simp [u1ChainFold, u1StepLoop_append_singleton]

/-- Deterministic reverse-step collision finder for `u1ChainFold`: walks backward from the final
boundary step and returns the exact `u1StepCustomization` frame pair where two chains first diverge. -/
def u1ChainCollisionRev (w₁ p₁ : Digest256) (pl₁ : Nat) :
    List Digest256 → (w₂ p₂ : Digest256) → (pl₂ : Nat) → List Digest256 → Frames
  | [], w₂, p₂, pl₂, _ =>
      ⟨u1StepCustomization,
       u1StepFrameCodec.encode (0, w₁, pl₁, p₁),
       u1StepFrameCodec.encode (0, w₂, pl₂, p₂)⟩
  | last₁ :: revPre₁, w₂, p₂, pl₂, last₂ :: revPre₂ =>
      let pre₁ := revPre₁.reverse
      let pre₂ := revPre₂.reverse
      let f₁ := u1StepFrameCodec.encode (1, u1ChainFold w₁ p₁ pl₁ pre₁, pre₁.length, last₁)
      let f₂ := u1StepFrameCodec.encode (1, u1ChainFold w₂ p₂ pl₂ pre₂, pre₂.length, last₂)
      if f₁ = f₂ then
        u1ChainCollisionRev w₁ p₁ pl₁ revPre₁ w₂ p₂ pl₂ revPre₂
      else
        ⟨u1StepCustomization, f₁, f₂⟩
  | last₁ :: revPre₁, w₂, p₂, pl₂, [] =>
      ⟨u1StepCustomization,
       u1StepFrameCodec.encode (1, u1ChainFold w₁ p₁ pl₁ revPre₁.reverse, revPre₁.length, last₁),
       u1StepFrameCodec.encode (0, w₂, pl₂, p₂)⟩

/-- Input-pinned collision frames between two `u1ChainFold` evaluations. -/
def u1ChainCollisionFrames
    (w₁ p₁ : Digest256) (pl₁ : Nat) (bs₁ : List Digest256)
    (w₂ p₂ : Digest256) (pl₂ : Nat) (bs₂ : List Digest256) : Frames :=
  u1ChainCollisionRev w₁ p₁ pl₁ bs₁.reverse w₂ p₂ pl₂ bs₂.reverse

/-- Input-pinned collision event for `u1ChainFold`. -/
def U1ChainCollision
    (w₁ p₁ : Digest256) (pl₁ : Nat) (bs₁ : List Digest256)
    (w₂ p₂ : Digest256) (pl₂ : Nat) (bs₂ : List Digest256) : Prop :=
  let f := u1ChainCollisionFrames w₁ p₁ pl₁ bs₁ w₂ p₂ pl₂ bs₂
  FramedXofCollision cshakeC f.customization f.left f.right

private theorem u1ChainCollisionRev_sound
    (w₁ p₁ : Digest256) (pl₁ : Nat) (rev₁ : List Digest256)
    (w₂ p₂ : Digest256) (pl₂ : Nat) (rev₂ : List Digest256) :
    rev₁.length = rev₂.length →
    u1ChainFold w₁ p₁ pl₁ rev₁.reverse = u1ChainFold w₂ p₂ pl₂ rev₂.reverse →
    (w₁ = w₂ ∧ pl₁ = pl₂ ∧ p₁ = p₂ ∧ rev₁ = rev₂) ∨
      let f := u1ChainCollisionRev w₁ p₁ pl₁ rev₁ w₂ p₂ pl₂ rev₂
      FramedXofCollision cshakeC f.customization f.left f.right := by
  induction rev₁ generalizing rev₂ with
  | nil =>
      intro hlen hchain
      cases rev₂ with
      | cons _ _ => simp at hlen
      | nil =>
          simp only [List.reverse_nil, u1ChainFold, u1StepLoop, u1InitAcc] at hchain
          rcases cshake256D256_eq_or_collision _ _ _ hchain with hfr | hcol
          · have hinj := streamCodec_encode_injective u1StepFrameCodec hfr
            simp only [Prod.mk.injEq, true_and] at hinj
            exact Or.inl ⟨hinj.1, hinj.2.1, hinj.2.2, rfl⟩
          · exact Or.inr hcol
  | cons last₁ revPre₁ ih =>
      intro hlen hchain
      cases rev₂ with
      | nil => simp at hlen
      | cons last₂ revPre₂ =>
          have hpreLen : revPre₁.length = revPre₂.length := by
            simp only [List.length_cons] at hlen
            omega
          rw [List.reverse_cons, List.reverse_cons,
            u1ChainFold_append_singleton, u1ChainFold_append_singleton] at hchain
          unfold u1StepAcc at hchain
          change (w₁ = w₂ ∧ pl₁ = pl₂ ∧ p₁ = p₂ ∧ last₁ :: revPre₁ = last₂ :: revPre₂) ∨
            let f := u1ChainCollisionRev w₁ p₁ pl₁ (last₁ :: revPre₁) w₂ p₂ pl₂ (last₂ :: revPre₂)
            FramedXofCollision cshakeC f.customization f.left f.right
          simp only [u1ChainCollisionRev]
          by_cases hfeq :
              u1StepFrameCodec.encode (1, u1ChainFold w₁ p₁ pl₁ revPre₁.reverse, revPre₁.reverse.length, last₁) =
              u1StepFrameCodec.encode (1, u1ChainFold w₂ p₂ pl₂ revPre₂.reverse, revPre₂.reverse.length, last₂)
          · simp only [hfeq, ↓reduceIte]
            have hinj := streamCodec_encode_injective u1StepFrameCodec hfeq
            simp only [Prod.mk.injEq, true_and] at hinj
            rcases hinj with ⟨hacc, _, hlast⟩
            subst hlast
            rcases ih revPre₂ hpreLen hacc with ⟨hw, hpl, hp, hrev⟩ | hcolPre
            · exact Or.inl ⟨hw, hpl, hp, congrArg (List.cons last₁) hrev⟩
            · exact Or.inr hcolPre
          · simp only [hfeq, ↓reduceIte]
            rcases cshake256D256_eq_or_collision _ _ _ hchain with hfr | hcol
            · exact False.elim (hfeq hfr)
            · exact Or.inr hcol

/-- Inductive unrolling of `u1ChainFold`: equal chain roots over equal-length boundary lists either
force identical `(weightRoot, promptLen, promptRoot, boundaryRoots)` or collide at the exact frames
`u1ChainCollisionFrames` computes from the two chains. -/
theorem u1ChainFold_eq_or_collision
    (w₁ p₁ : Digest256) (pl₁ : Nat) (bs₁ : List Digest256)
    (w₂ p₂ : Digest256) (pl₂ : Nat) (bs₂ : List Digest256)
    (hlen : bs₁.length = bs₂.length)
    (hchain : u1ChainFold w₁ p₁ pl₁ bs₁ = u1ChainFold w₂ p₂ pl₂ bs₂) :
    (w₁ = w₂ ∧ pl₁ = pl₂ ∧ p₁ = p₂ ∧ bs₁ = bs₂) ∨
    U1ChainCollision w₁ p₁ pl₁ bs₁ w₂ p₂ pl₂ bs₂ := by
  have hrevLen : bs₁.reverse.length = bs₂.reverse.length := by simp [hlen]
  have hrevChain : u1ChainFold w₁ p₁ pl₁ bs₁.reverse.reverse =
      u1ChainFold w₂ p₂ pl₂ bs₂.reverse.reverse := by
    simpa [List.reverse_reverse] using hchain
  rcases u1ChainCollisionRev_sound w₁ p₁ pl₁ bs₁.reverse w₂ p₂ pl₂ bs₂.reverse
      hrevLen hrevChain with ⟨hw, hpl, hp, hrevEq⟩ | hcol
  · exact Or.inl ⟨hw, hpl, hp, List.reverse_inj.mp hrevEq⟩
  · exact Or.inr hcol

/-- Input-pinned collision frames between two `u1TurnHead` evaluations. -/
def u1TurnHeadCollisionFrames
    (w₁ p₁ : Digest256) (pl₁ : Nat) (bs₁ : List Digest256) (pf₁ : Digest256) (rl₁ : Nat) (rr₁ : Digest256)
    (w₂ p₂ : Digest256) (pl₂ : Nat) (bs₂ : List Digest256) (pf₂ : Digest256) (rl₂ : Nat) (rr₂ : Digest256) :
    Frames :=
  let out₁ := u1OutFrameCodec.encode (u1ChainFold w₁ p₁ pl₁ bs₁, bs₁.length, pf₁, rl₁, rr₁)
  let out₂ := u1OutFrameCodec.encode (u1ChainFold w₂ p₂ pl₂ bs₂, bs₂.length, pf₂, rl₂, rr₂)
  if out₁ = out₂ then
    u1ChainCollisionFrames w₁ p₁ pl₁ bs₁ w₂ p₂ pl₂ bs₂
  else
    ⟨u1OutCustomization, out₁, out₂⟩

/-- Input-pinned collision event for `u1TurnHead` (never an existential over `cshakeC`). -/
def U1TurnHeadCollision
    (w₁ p₁ : Digest256) (pl₁ : Nat) (bs₁ : List Digest256) (pf₁ : Digest256) (rl₁ : Nat) (rr₁ : Digest256)
    (w₂ p₂ : Digest256) (pl₂ : Nat) (bs₂ : List Digest256) (pf₂ : Digest256) (rl₂ : Nat) (rr₂ : Digest256) :
    Prop :=
  let f := u1TurnHeadCollisionFrames w₁ p₁ pl₁ bs₁ pf₁ rl₁ rr₁ w₂ p₂ pl₂ bs₂ pf₂ rl₂ rr₂
  FramedXofCollision cshakeC f.customization f.left f.right

/-- **Full `U1` Turn-Head Collision Extraction (`u1TurnHead_eq_or_collision`):**
Two `U1` boundary chains hashing to one `turnChainRoot` agree on `weightRoot`, `promptLen`,
`promptRoot`, every intermediate layer boundary `boundaryRoots[0 .. L]`, `u1ProofDigest`, `rawLen`,
and `rawRoot` — OR collide at the exact input-pinned frames `u1TurnHeadCollisionFrames` computes! -/
theorem u1TurnHead_eq_or_collision
    (w₁ p₁ : Digest256) (pl₁ : Nat) (bs₁ : List Digest256) (pf₁ : Digest256) (rl₁ : Nat) (rr₁ : Digest256)
    (w₂ p₂ : Digest256) (pl₂ : Nat) (bs₂ : List Digest256) (pf₂ : Digest256) (rl₂ : Nat) (rr₂ : Digest256)
    (hhead : u1TurnHead w₁ p₁ pl₁ bs₁ pf₁ rl₁ rr₁ = u1TurnHead w₂ p₂ pl₂ bs₂ pf₂ rl₂ rr₂) :
    (w₁ = w₂ ∧ pl₁ = pl₂ ∧ p₁ = p₂ ∧ bs₁ = bs₂ ∧ pf₁ = pf₂ ∧ rl₁ = rl₂ ∧ rr₁ = rr₂) ∨
    U1TurnHeadCollision w₁ p₁ pl₁ bs₁ pf₁ rl₁ rr₁ w₂ p₂ pl₂ bs₂ pf₂ rl₂ rr₂ := by
  unfold u1TurnHead at hhead
  unfold U1TurnHeadCollision u1TurnHeadCollisionFrames
  dsimp only
  by_cases hout :
      u1OutFrameCodec.encode (u1ChainFold w₁ p₁ pl₁ bs₁, bs₁.length, pf₁, rl₁, rr₁) =
      u1OutFrameCodec.encode (u1ChainFold w₂ p₂ pl₂ bs₂, bs₂.length, pf₂, rl₂, rr₂)
  · simp only [hout, ↓reduceIte]
    have hinj := streamCodec_encode_injective u1OutFrameCodec hout
    simp only [Prod.mk.injEq] at hinj
    rcases hinj with ⟨hchain, hlen, hpf, hrl, hrr⟩
    rcases u1ChainFold_eq_or_collision w₁ p₁ pl₁ bs₁ w₂ p₂ pl₂ bs₂ hlen hchain with
      ⟨hw, hpl, hp, hbs⟩ | hcolChain
    · exact Or.inl ⟨hw, hpl, hp, hbs, hpf, hrl, hrr⟩
    · exact Or.inr hcolChain
  · simp only [hout, ↓reduceIte]
    rcases cshake256D256_eq_or_collision _ _ _ hhead with hfr | hcol
    · exact False.elim (hout hfr)
    · exact Or.inr hcol

/-! ## §4. Executable Byte-Stream Turn Verifier & End-to-End Soundness Theorem -/

/-- Resolve compact `Nat` rule indices into concrete `AttrRule` productions of `rules`. -/
def resolveRuleIndices {T NT SemOp : Type}
    (rules : List (AttrRule T NT SemOp)) : List Nat → Option (List (AttrRule T NT SemOp))
  | [] => some []
  | idx :: rest => do
      let r ← rules[idx]?
      let rs ← resolveRuleIndices rules rest
      some (r :: rs)

/-- Grammar-parameterized executable turn verifier (specialized at `miniJsonCfg` below). -/
def verifyAgentTurnWithCfg {NT SemOp : Type} [DecidableEq NT] [DecidableEq SemOp]
    (g : AttrCfg UInt8 NT SemOp MiniValue)
    (stmt : VerifiableAgentTurnStmt) (rcpt : VerifiableAgentTurnReceipt) : Bool :=
  decide (0 < stmt.numLayers) &&
  decide (rcpt.boundaryRoots.length = stmt.numLayers + 1) &&
  decide (rcpt.auditedLayer < stmt.numLayers) &&
  decide (rcpt.auditedLayer =
    u1VrfSelectLayer stmt.weightRoot rcpt.boundaryRoots stmt.cleanRoot stmt.numLayers) &&
  decide (rcpt.boundaryRoots[rcpt.auditedLayer]? = some rcpt.auditedBInRoot) &&
  decide (rcpt.boundaryRoots[rcpt.auditedLayer + 1]? = some rcpt.auditedBOutRoot) &&
  decide (rcpt.promptBytes.length = stmt.promptLength) &&
  decide (contentCommit rcpt.promptBytes = ofDigest256 stmt.promptRoot) &&
  decide (u1TurnHead stmt.weightRoot stmt.promptRoot stmt.promptLength
    rcpt.boundaryRoots rcpt.u1ProofDigest stmt.rawLength stmt.rawRoot = stmt.turnChainRoot) &&
  ll1Deterministic g &&
  allRulesSafe defaultSecretRules &&
  decide (rcpt.wRaw.length = stmt.rawLength) &&
  decide (contentCommit rcpt.wRaw = ofDigest256 stmt.rawRoot) &&
  decide (rcpt.wClean.length = stmt.cleanLength) &&
  decide (contentCommit rcpt.wClean = ofDigest256 stmt.cleanRoot) &&
  decide (rcpt.wClean = redactBytes defaultSecretRules rcpt.wRaw) &&
  match resolveRuleIndices g.rules rcpt.ruleIndices with
  | none => false
  | some rs => decide (execAttrReplay g rs rcpt.wClean = some stmt.claimedAst)

/-- Canonical `miniJsonCfg` turn verifier. -/
def verifyAgentTurn (stmt : VerifiableAgentTurnStmt) (rcpt : VerifiableAgentTurnReceipt) : Bool :=
  verifyAgentTurnWithCfg miniJsonCfg stmt rcpt

/-- **Top-Level Executable Byte-Stream Verifier (`verifyAgentTurnBytes`):**
parses `VASTMT01` and `VAGENT01` directly from raw octets (refusing any non-canonical spelling or
trailing bytes) and verifies the full `U1` + `RewriteCert` + LL(1) `CotToolCall` turn weld. -/
def verifyAgentTurnBytes (stmtBytes receiptBytes : List UInt8) : Bool :=
  match decodeTurnStmt stmtBytes, decodeTurnReceipt receiptBytes with
  | some stmt, some rcpt => verifyAgentTurn stmt rcpt
  | _, _ => false

/-- Named execution objects committed to `stmt`'s public roots. -/
def CommitsAgentTurnChain (stmt : VerifiableAgentTurnStmt)
    (namedPrompt : List UInt8) (namedBoundaries : List Digest256) (namedProofDigest : Digest256)
    (namedRaw namedClean : List UInt8) : Prop :=
  namedPrompt.length = stmt.promptLength ∧
  contentCommit namedPrompt = ofDigest256 stmt.promptRoot ∧
  u1TurnHead stmt.weightRoot stmt.promptRoot stmt.promptLength
    namedBoundaries namedProofDigest stmt.rawLength stmt.rawRoot = stmt.turnChainRoot ∧
  namedRaw.length = stmt.rawLength ∧
  contentCommit namedRaw = ofDigest256 stmt.rawRoot ∧
  namedClean.length = stmt.cleanLength ∧
  contentCommit namedClean = ofDigest256 stmt.cleanRoot

/-- Input-pinned collision disjunct for `verifyAgentTurnBytes_sound_or_collision`: names the exact
pair of `cSHAKE256` Merkle trees or `U1` hash-chain frames where `rcpt` and the named trace collide
(never an existential over `cshakeC`, which pigeonhole would inhabit). -/
def AgentTurnWeldCollision
    (stmt : VerifiableAgentTurnStmt) (rcpt : VerifiableAgentTurnReceipt)
    (namedPrompt : List UInt8) (namedBoundaries : List Digest256)
    (namedProofDigest : Digest256) (namedRaw namedClean : List UInt8) : Prop :=
  DenseCollision (namedPrompt.map UInt8.toNat) (rcpt.promptBytes.map UInt8.toNat) ∨
  U1TurnHeadCollision
    stmt.weightRoot stmt.promptRoot stmt.promptLength
    namedBoundaries namedProofDigest stmt.rawLength stmt.rawRoot
    stmt.weightRoot stmt.promptRoot stmt.promptLength
    rcpt.boundaryRoots rcpt.u1ProofDigest stmt.rawLength stmt.rawRoot ∨
  DenseCollision (namedRaw.map UInt8.toNat) (rcpt.wRaw.map UInt8.toNat) ∨
  DenseCollision (namedClean.map UInt8.toNat) (rcpt.wClean.map UInt8.toNat)

/-- **Capstone Theorem (`verifyAgentTurnBytes_sound_or_collision`):**
Whenever `verifyAgentTurnBytes stmtBytes receiptBytes = true`:
1. `stmtBytes` and `receiptBytes` decode uniquely to canonical `(stmt, rcpt)` (`encodeTurnStmt stmt = stmtBytes`,
   `encodeTurnReceipt rcpt = receiptBytes`), AND
2. For **every** named `(namedPrompt, namedBoundaries, namedProofDigest, namedRaw, namedClean)`
   matching `stmt`'s public commitments (`CommitsAgentTurnChain`), EITHER:
   - **(a) `U1` Boundary-Chain & Prompt/Output Commitment Weld:**
     `namedPrompt = rcpt.promptBytes`, `namedBoundaries = rcpt.boundaryRoots`,
     `namedProofDigest = rcpt.u1ProofDigest`, `namedRaw = rcpt.wRaw`, `namedClean = rcpt.wClean`,
     `0 < stmt.numLayers`, `namedBoundaries.length = stmt.numLayers + 1`,
     `rcpt.auditedLayer < stmt.numLayers` equals `u1VrfSelectLayer ...`, and `namedBoundaries`
     matches `(rcpt.auditedBInRoot, rcpt.auditedBOutRoot)` at `(auditedLayer, auditedLayer + 1)`;
   - **(b) Canonical Secret Sanitization & Universal Padded-Complement Absence:**
     `namedClean = redactBytes defaultSecretRules namedRaw`, `RedactsTo defaultSecretRules namedRaw namedClean`,
     every `rt ∈ defaultSecretRules` satisfies `AbsentPlain namedClean rt.pat` AND
     `MatchesRegex namedClean (Regex.paddedComplement (Regex.literal rt.pat))`, and clean raw
     inputs suffer zero mangling (`(∀ r ∈ defaultSecretRules, AbsentPlain namedRaw r.pat) → namedClean = namedRaw`);
   - **(c) Unique LL(1) `MiniValue` AST & Parse Extraction:**
     `∃ rs, resolveRuleIndices miniJsonCfg.rules rcpt.ruleIndices = some rs ∧ AttrReplay miniJsonCfg rs namedClean stmt.claimedAst ∧ namedClean ∈ miniJsonCfg.toCfg.language ∧ ∀ rs' ast', AttrReplay miniJsonCfg rs' namedClean ast' → ast' = stmt.claimedAst ∧ rs' = rs` —
   **OR** the input-pinned `AgentTurnWeldCollision` holds! -/
theorem verifyAgentTurnBytes_sound_or_collision
    (stmtBytes receiptBytes : List UInt8)
    (hver : verifyAgentTurnBytes stmtBytes receiptBytes = true) :
    ∃ (stmt : VerifiableAgentTurnStmt) (rcpt : VerifiableAgentTurnReceipt),
      decodeTurnStmt stmtBytes = some stmt ∧
      decodeTurnReceipt receiptBytes = some rcpt ∧
      encodeTurnStmt stmt = stmtBytes ∧
      encodeTurnReceipt rcpt = receiptBytes ∧
      ∀ (namedPrompt : List UInt8) (namedBoundaries : List Digest256)
        (namedProofDigest : Digest256) (namedRaw namedClean : List UInt8),
        CommitsAgentTurnChain stmt namedPrompt namedBoundaries namedProofDigest namedRaw namedClean →
        ((namedPrompt = rcpt.promptBytes ∧
          namedBoundaries = rcpt.boundaryRoots ∧
          namedProofDigest = rcpt.u1ProofDigest ∧
          namedRaw = rcpt.wRaw ∧
          namedClean = rcpt.wClean ∧
          0 < stmt.numLayers ∧
          namedBoundaries.length = stmt.numLayers + 1 ∧
          rcpt.auditedLayer < stmt.numLayers ∧
          rcpt.auditedLayer =
            u1VrfSelectLayer stmt.weightRoot namedBoundaries stmt.cleanRoot stmt.numLayers ∧
          namedBoundaries[rcpt.auditedLayer]? = some rcpt.auditedBInRoot ∧
          namedBoundaries[rcpt.auditedLayer + 1]? = some rcpt.auditedBOutRoot) ∧
         (namedClean = redactBytes defaultSecretRules namedRaw ∧
          RedactsTo defaultSecretRules namedRaw namedClean ∧
          (∀ rt ∈ defaultSecretRules,
            AbsentPlain namedClean rt.pat ∧
            MatchesRegex namedClean (Regex.paddedComplement (Regex.literal rt.pat)) ∧
            Regex.derives namedClean (Regex.paddedComplement (Regex.literal rt.pat)) = true) ∧
          ((∀ r ∈ defaultSecretRules, AbsentPlain namedRaw r.pat) → namedClean = namedRaw)) ∧
         (∃ rs, resolveRuleIndices miniJsonCfg.rules rcpt.ruleIndices = some rs ∧
            AttrReplay miniJsonCfg rs namedClean stmt.claimedAst ∧
            namedClean ∈ miniJsonCfg.toCfg.language ∧
            (∀ (rs' : List (AttrRule UInt8 MiniNT MiniOp)) (ast' : MiniValue),
              AttrReplay miniJsonCfg rs' namedClean ast' →
                ast' = stmt.claimedAst ∧ rs' = rs))) ∨
        AgentTurnWeldCollision stmt rcpt namedPrompt namedBoundaries namedProofDigest namedRaw namedClean := by
  unfold verifyAgentTurnBytes at hver
  cases hs : decodeTurnStmt stmtBytes with
  | none => simp [hs] at hver
  | some stmt =>
      cases hr : decodeTurnReceipt receiptBytes with
      | none => simp [hs, hr] at hver
      | some rcpt =>
          simp only [hs, hr] at hver
          refine ⟨stmt, rcpt, rfl, rfl,
            (decodeTurnStmt_eq_some_iff stmtBytes stmt).mp hs,
            (decodeTurnReceipt_eq_some_iff receiptBytes rcpt).mp hr, ?_⟩
          intro namedPrompt namedBoundaries namedProofDigest namedRaw namedClean hcomm
          unfold verifyAgentTurn verifyAgentTurnWithCfg at hver
          cases hres : resolveRuleIndices miniJsonCfg.rules rcpt.ruleIndices with
          | none => simp [hres] at hver
          | some rs =>
              rw [hres] at hver
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hver
              rcases hver with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hLpos, hbLen⟩, haLt⟩, haVrf⟩, hbIn⟩, hbOut⟩,
                hpLen⟩, hpRoot⟩, hturnHead⟩, hll1⟩, hsafe⟩, hrLen⟩, hrRoot⟩, hcLen⟩, hcRoot⟩,
                hred⟩, hexec⟩
              rcases hcomm with ⟨hnpLen, hnpRoot, hnturnHead, hnrLen, hnrRoot, hncLen, hncRoot⟩
              rcases contentCommit_eq_or_denseCollision
                  (hnpLen.trans hpLen.symm) (hnpRoot.trans hpRoot.symm) with hpEq | hpCol
              · rcases u1TurnHead_eq_or_collision
                    stmt.weightRoot stmt.promptRoot stmt.promptLength
                    namedBoundaries namedProofDigest stmt.rawLength stmt.rawRoot
                    stmt.weightRoot stmt.promptRoot stmt.promptLength
                    rcpt.boundaryRoots rcpt.u1ProofDigest stmt.rawLength stmt.rawRoot
                    (hnturnHead.trans hturnHead.symm) with ⟨_, _, _, hbEq, hpfEq, _, _⟩ | hu1Col
                · rcases contentCommit_eq_or_denseCollision
                      (hnrLen.trans hrLen.symm) (hnrRoot.trans hrRoot.symm) with hrEq | hrCol
                  · rcases contentCommit_eq_or_denseCollision
                        (hncLen.trans hcLen.symm) (hncRoot.trans hcRoot.symm) with hcEq | hcCol
                    · left
                      subst hpEq hbEq hpfEq hrEq hcEq
                      have hrep : AttrReplay miniJsonCfg rs rcpt.wClean stmt.claimedAst :=
                        (execAttrReplay_iff miniJsonCfg rs rcpt.wClean stmt.claimedAst).mp hexec
                      refine ⟨⟨rfl, rfl, rfl, rfl, rfl, hLpos, hbLen, haLt, haVrf, hbIn, hbOut⟩,
                        ⟨hred, hred ▸ redactsTo_redactBytes defaultSecretRules rcpt.wRaw, ?_,
                          fun hcl => hred.trans (redactBytes_preserves_clean_plain defaultSecretRules rcpt.wRaw hcl)⟩,
                        ⟨rs, rfl, hrep, attrReplay_mem_language hrep,
                          fun rs' ast' hrep' => attrReplay_unique_of_ll1 miniJsonCfg hll1 hrep' hrep⟩⟩
                      intro rt hrt
                      have hsc := redactBytes_scrubs_padded_complement defaultSecretRules hsafe rt hrt rcpt.wRaw
                      rwa [← hred] at hsc
                    · exact Or.inr (Or.inr (Or.inr (Or.inr hcCol)))
                  · exact Or.inr (Or.inr (Or.inr (Or.inl hrCol)))
                · exact Or.inr (Or.inr (Or.inl hu1Col))
              · exact Or.inr (Or.inl hpCol)

/-! ## §5. Concrete `CertificateComposition` (`P8` `Produced`) Weld Grounded on `verifyAgentTurnBytes` -/

/-- Concrete `(length, contentCommit)` content scheme over SP 800-185 `cSHAKE256`. -/
def lengthRootScheme (bindAdv : Nat → ℝ) (hnn : ∀ q, 0 ≤ bindAdv q) :
    ContentScheme UInt8 (Nat × Digest) (List UInt8) where
  commit w := (w.length, contentCommit w)
  openAt w _ := w
  openLen w := w
  verifyOpen c i v w := decide (w.length = c.1 ∧ contentCommit w = c.2 ∧ w[i]? = some v)
  verifyLen c n w := decide (w.length = c.1 ∧ contentCommit w = c.2 ∧ n = c.1)
  complete w i hi := by simp [List.getElem?_eq_getElem hi]
  completeLen w := by simp
  bindAdv := bindAdv
  bindAdv_nonneg := hnn

/-- Non-trivial raw-output policy predicate discharged by `verifyAgentTurnBytes`:
`wClean := redactBytes defaultSecretRules wRaw` matches `(stmt.cleanLength, stmt.cleanRoot)`, is
provably free of all 5 secret classes (`AbsentPlain` + `Regex.paddedComplement`), and parses
uniquely to `stmt.claimedAst` under `miniJsonCfg`. -/
def CertifiedSanitizedTurn (stmt : VerifiableAgentTurnStmt) (wRaw : List UInt8) : Prop :=
  let wClean := redactBytes defaultSecretRules wRaw
  wClean.length = stmt.cleanLength ∧
  contentCommit wClean = ofDigest256 stmt.cleanRoot ∧
  (∀ rt ∈ defaultSecretRules,
    AbsentPlain wClean rt.pat ∧
    MatchesRegex wClean (Regex.paddedComplement (Regex.literal rt.pat))) ∧
  (∃ rs, AttrReplay miniJsonCfg rs wClean stmt.claimedAst ∧
    ∀ (rs' : List (AttrRule UInt8 MiniNT MiniOp)) (ast' : MiniValue),
      AttrReplay miniJsonCfg rs' wClean ast' → ast' = stmt.claimedAst ∧ rs' = rs)

/-- Adapter binding `verifyAgentTurnBytes` to raw commitment `cRaw : Nat × Digest`. -/
def verifyTurnBytesAtRaw (stmt : VerifiableAgentTurnStmt)
    (cRaw : Nat × Digest) (receiptBytes : List UInt8) : Bool :=
  decide (cRaw = (stmt.rawLength, ofDigest256 stmt.rawRoot)) &&
  verifyAgentTurnBytes (encodeTurnStmt stmt) receiptBytes

/-- Straightline extractor reading `rcpt.wRaw` directly from a decoded `VAGENT01` receipt. -/
def extractTurnRaw {Log : Type} (_ : Nat × Digest) (receiptBytes : List UInt8) (_ : Log) :
    List UInt8 :=
  match decodeTurnReceipt receiptBytes with
  | some rcpt => rcpt.wRaw
  | none => []

/-- Straightline receipt-witness grounding in query environment `E`:
whenever `verifyTurnBytesAtRaw stmt (c ω) (π ω) = true`, the decoded receipt witness
`extractTurnRaw (c ω) (π ω) (log ω)` is grounded in `log ω` up to error `ε_ground q`
(e.g., `ε_ground = 0` on preimage-logged transcripts or `unrestrictedEnv`, and `2^{-256}` in ROM). -/
def TurnReceiptGrounded (E : QueryEnv UInt8) (stmt : VerifiableAgentTurnStmt)
    (ε_ground : Nat → ℝ) : Prop :=
  ∀ (q : Nat) (c : E.Coins q → Nat × Digest) (π : E.Coins q → List UInt8)
    (log : E.Coins q → E.Log),
    E.ValidLog q log →
    BindingGame.prob (fun ω =>
      verifyTurnBytesAtRaw stmt (c ω) (π ω) = true ∧
      ¬ E.Grounded (log ω) (extractTurnRaw (c ω) (π ω) (log ω)))
      ≤ ε_ground q

theorem turnReceiptGrounded_unrestricted (stmt : VerifiableAgentTurnStmt) :
    TurnReceiptGrounded (unrestrictedEnv UInt8) stmt (fun _ => 0) := by
  intro q c π log _
  have hfalse : ∀ ω : (unrestrictedEnv UInt8).Coins q,
      ¬ (verifyTurnBytesAtRaw stmt (c ω) (π ω) = true ∧
          ¬ (unrestrictedEnv UInt8).Grounded (log ω) (extractTurnRaw (c ω) (π ω) (log ω))) :=
    fun _ ⟨_, hng⟩ => hng trivial
  rw [prob_eq_zero_of_false hfalse]

/-- Deterministic witness soundness of `verifyTurnBytesAtRaw`: any accepted `VAGENT01` byte stream
commits to `cRaw` under `lengthRootScheme` and satisfies `CertifiedSanitizedTurn stmt`. -/
theorem verifyTurnBytesAtRaw_sound_det
    (stmt : VerifiableAgentTurnStmt) (cRaw : Nat × Digest) (receiptBytes : List UInt8)
    {Log : Type} (l : Log)
    (bindAdv : Nat → ℝ) (hnn : ∀ q, 0 ≤ bindAdv q)
    (hv : verifyTurnBytesAtRaw stmt cRaw receiptBytes = true) :
    (lengthRootScheme bindAdv hnn).commit (extractTurnRaw cRaw receiptBytes l) = cRaw ∧
    CertifiedSanitizedTurn stmt (extractTurnRaw cRaw receiptBytes l) := by
  unfold verifyTurnBytesAtRaw at hv
  rw [Bool.and_eq_true, decide_eq_true_eq] at hv
  rcases hv with ⟨hcEq, hverB⟩
  unfold verifyAgentTurnBytes at hverB
  rw [decodeTurnStmt_encodeTurnStmt] at hverB
  cases hr : decodeTurnReceipt receiptBytes with
  | none => simp [hr] at hverB
  | some rcpt =>
      simp only [hr] at hverB
      unfold verifyAgentTurn verifyAgentTurnWithCfg at hverB
      cases hres : resolveRuleIndices miniJsonCfg.rules rcpt.ruleIndices with
      | none => simp [hres] at hverB
      | some rs =>
          rw [hres] at hverB
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hverB
          rcases hverB with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩,
            _⟩, _⟩, _⟩, hll1⟩, hsafe⟩, hrLen⟩, hrRoot⟩, hcLen⟩, hcRoot⟩,
            hred⟩, hexec⟩
          have hrep : AttrReplay miniJsonCfg rs rcpt.wClean stmt.claimedAst :=
            (execAttrReplay_iff miniJsonCfg rs rcpt.wClean stmt.claimedAst).mp hexec
          simp only [extractTurnRaw, hr, lengthRootScheme, CertifiedSanitizedTurn]
          refine ⟨Prod.ext hrLen hrRoot |>.trans hcEq.symm, ?_⟩
          rw [← hred]
          refine ⟨hcLen, hcRoot, ?_, ⟨rs, hrep,
            fun rs' ast' hrep' => attrReplay_unique_of_ll1 miniJsonCfg hll1 hrep' hrep⟩⟩
          intro rt hrt
          have hsc := redactBytes_scrubs_padded_complement defaultSecretRules hsafe rt hrt rcpt.wRaw
          rw [← hred] at hsc
          exact ⟨hsc.1, hsc.2.1⟩

/-- **`verifyAgentTurnBytes_certSound` (`QueryEnv`-parametric):** for **every** `E : QueryEnv UInt8`,
`verifyTurnBytesAtRaw stmt` is a genuine straightline `CertSound` verifier over `lengthRootScheme`
at error `ε_ground` for `CertifiedSanitizedTurn stmt`. -/
theorem verifyAgentTurnBytes_certSound
    (E : QueryEnv UInt8)
    (stmt : VerifiableAgentTurnStmt)
    (bindAdv ε_ground : Nat → ℝ) (hnn : ∀ q, 0 ≤ bindAdv q)
    (hground : TurnReceiptGrounded E stmt ε_ground) :
    CertSound E (lengthRootScheme bindAdv hnn)
      (verifyTurnBytesAtRaw stmt) (CertifiedSanitizedTurn stmt) ε_ground := by
  refine ⟨extractTurnRaw, fun q c π log hlog => ?_⟩
  have hsub : BindingGame.prob (fun ω =>
      verifyTurnBytesAtRaw stmt (c ω) (π ω) = true ∧
        ¬ (E.Grounded (log ω) (extractTurnRaw (c ω) (π ω) (log ω)) ∧
            (lengthRootScheme bindAdv hnn).commit (extractTurnRaw (c ω) (π ω) (log ω)) = c ω ∧
            CertifiedSanitizedTurn stmt (extractTurnRaw (c ω) (π ω) (log ω)))) ≤
      BindingGame.prob (fun ω =>
        verifyTurnBytesAtRaw stmt (c ω) (π ω) = true ∧
        ¬ E.Grounded (log ω) (extractTurnRaw (c ω) (π ω) (log ω))) := by
    apply BindingGame.prob_mono
    intro ω ⟨hv, hbad⟩
    have hdet := verifyTurnBytesAtRaw_sound_det stmt (c ω) (π ω) (log ω) bindAdv hnn hv
    exact ⟨hv, fun hg => hbad ⟨hg, hdet.1, hdet.2⟩⟩
  exact le_trans hsub (hground q c π log hlog)

/-- **`P8` Grounded End-to-End Turn Weld (`verifiableAgentTurn_produced_weld`):**
Parameterized over **arbitrary `E : QueryEnv UInt8`** (eliminating `unrestrictedEnv` 33-byte pigeonhole!)
and explicitly binding model identity `stmt.weightRoot` and prompt commitment
`(stmt.promptLength, ofDigest256 stmt.promptRoot)` between `V_u1` and `verifyTurnBytesAtRaw stmt`
via `CertificateComposition.cert_produced_weld` (`P8`) at sharp error `ε_u1 q + ε_cert q + bindAdv q`! -/
theorem verifiableAgentTurn_produced_weld
    {U1Proof : Type}
    (E : QueryEnv UInt8)
    (stmt : VerifiableAgentTurnStmt)
    (bindAdv ε_cert : Nat → ℝ) (hnn : ∀ q, 0 ≤ bindAdv q)
    {IsQwenTurnOutput : Digest256 → (Nat × Digest) → List UInt8 → Prop}
    {V_u1 : Digest256 → (Nat × Digest) → (Nat × Digest) → U1Proof → Bool}
    {ε_u1 : Nat → ℝ}
    (hu1 : ProducedSound E (lengthRootScheme bindAdv hnn)
      IsQwenTurnOutput V_u1 ε_u1)
    (hcert : CertSound E (lengthRootScheme bindAdv hnn)
      (verifyTurnBytesAtRaw stmt) (CertifiedSanitizedTurn stmt) ε_cert)
    (hbind : BindSound E (lengthRootScheme bindAdv hnn)) :
    ∃ ext_out : Digest256 → (Nat × Digest) → (Nat × Digest) → U1Proof → E.Log → List UInt8,
      ∀ (q : Nat)
        (cout cout' : E.Coins q → Nat × Digest)
        (πu1 : E.Coins q → U1Proof) (πrcpt : E.Coins q → List UInt8)
        (log : E.Coins q → E.Log),
        E.ValidLog q log →
        let mStmt := stmt.weightRoot
        let cPrompt := (stmt.promptLength, ofDigest256 stmt.promptRoot)
        BindingGame.prob (fun ω =>
          (V_u1 mStmt cPrompt (cout ω) (πu1 ω) &&
           verifyTurnBytesAtRaw stmt (cout' ω) (πrcpt ω) &&
           decide (cout ω = cout' ω)) = true ∧
          ¬ (E.Grounded (log ω) (ext_out mStmt cPrompt (cout ω) (πu1 ω) (log ω)) ∧
              IsQwenTurnOutput mStmt cPrompt (ext_out mStmt cPrompt (cout ω) (πu1 ω) (log ω)) ∧
              CertifiedSanitizedTurn stmt (ext_out mStmt cPrompt (cout ω) (πu1 ω) (log ω))))
          ≤ ε_u1 q + ε_cert q + bindAdv q := by
  rcases cert_produced_weld hu1 hcert
      (bridgeSound_same_scheme (lengthRootScheme bindAdv hnn) hbind) with ⟨ext_out, hprob⟩
  refine ⟨ext_out, fun q cout cout' πu1 πrcpt log hlog => ?_⟩
  dsimp only
  have hb := hprob q (fun _ => stmt.weightRoot)
    (fun _ => (stmt.promptLength, ofDigest256 stmt.promptRoot))
    cout cout' πu1 πrcpt (fun _ => ()) log hlog
  exact le_trans hb (by simp [lengthRootScheme])

/-- Direct `TurnReceiptGrounded` corollary of `verifiableAgentTurn_produced_weld`. -/
theorem verifiableAgentTurn_produced_weld_of_grounded
    {U1Proof : Type}
    (E : QueryEnv UInt8)
    (stmt : VerifiableAgentTurnStmt)
    (bindAdv ε_ground : Nat → ℝ) (hnn : ∀ q, 0 ≤ bindAdv q)
    {IsQwenTurnOutput : Digest256 → (Nat × Digest) → List UInt8 → Prop}
    {V_u1 : Digest256 → (Nat × Digest) → (Nat × Digest) → U1Proof → Bool}
    {ε_u1 : Nat → ℝ}
    (hu1 : ProducedSound E (lengthRootScheme bindAdv hnn)
      IsQwenTurnOutput V_u1 ε_u1)
    (hground : TurnReceiptGrounded E stmt ε_ground)
    (hbind : BindSound E (lengthRootScheme bindAdv hnn)) :
    ∃ ext_out : Digest256 → (Nat × Digest) → (Nat × Digest) → U1Proof → E.Log → List UInt8,
      ∀ (q : Nat)
        (cout cout' : E.Coins q → Nat × Digest)
        (πu1 : E.Coins q → U1Proof) (πrcpt : E.Coins q → List UInt8)
        (log : E.Coins q → E.Log),
        E.ValidLog q log →
        let mStmt := stmt.weightRoot
        let cPrompt := (stmt.promptLength, ofDigest256 stmt.promptRoot)
        BindingGame.prob (fun ω =>
          (V_u1 mStmt cPrompt (cout ω) (πu1 ω) &&
           verifyTurnBytesAtRaw stmt (cout' ω) (πrcpt ω) &&
           decide (cout ω = cout' ω)) = true ∧
          ¬ (E.Grounded (log ω) (ext_out mStmt cPrompt (cout ω) (πu1 ω) (log ω)) ∧
              IsQwenTurnOutput mStmt cPrompt (ext_out mStmt cPrompt (cout ω) (πu1 ω) (log ω)) ∧
              CertifiedSanitizedTurn stmt (ext_out mStmt cPrompt (cout ω) (πu1 ω) (log ω))))
          ≤ ε_u1 q + ε_ground q + bindAdv q :=
  verifiableAgentTurn_produced_weld E stmt bindAdv ε_ground hnn hu1
    (verifyAgentTurnBytes_certSound E stmt bindAdv ε_ground hnn hground) hbind

/-! ## §6. Honest Completeness, Premise Inhabitation, & Soundness Falsifiers -/

private theorem resolveRuleIndices_map_idxOf {T NT SemOp : Type}
    [DecidableEq T] [DecidableEq NT] [DecidableEq SemOp]
    (rules : List (AttrRule T NT SemOp)) :
    ∀ (rs : List (AttrRule T NT SemOp)),
      (∀ r ∈ rs, r ∈ rules) →
      resolveRuleIndices rules (rs.map rules.idxOf) = some rs
  | [], _ => rfl
  | r :: rs, hmem => by
      have hr : r ∈ rules := hmem r (List.mem_cons_self ..)
      have hlt : rules.idxOf r < rules.length := List.idxOf_lt_length_of_mem hr
      have hget : rules[rules.idxOf r]? = some r := by
        rw [List.getElem?_eq_getElem hlt]
        exact congrArg some (List.getElem_idxOf hlt)
      have ih := resolveRuleIndices_map_idxOf rules rs
        (fun x hx => hmem x (List.mem_cons_of_mem _ hx))
      simp [resolveRuleIndices, hget, ih]

private theorem attrStackReplay_rules_mem {T NT SemOp Val : Type}
    {g : AttrCfg T NT SemOp Val} {rs : List (AttrRule T NT SemOp)}
    {w : List T} {cstk : List (WorkItem T NT SemOp)} {vstk : List Val} {ast : Val}
    (h : AttrStackReplay g rs w cstk vstk ast) : ∀ r ∈ rs, r ∈ g.rules := by
  induction h with
  | done _ => simp
  | term _ _ ih => exact ih
  | @rule r _ _ _ _ _ hr _ ih =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hr
      · exact ih x hx'
  | reduce _ _ _ _ ih => exact ih

/-- Build an honest `(VerifiableAgentTurnStmt, VerifiableAgentTurnReceipt)` pair from valid witness data. -/
def buildHonestAgentTurn
    (weightRoot : Digest256) (promptBytes : List UInt8)
    (numLayers : Nat) (boundaryRoots : List Digest256) (u1ProofDigest : Digest256)
    (wRaw : List UInt8) (rs : List (AttrRule UInt8 MiniNT MiniOp)) (ast : MiniValue) :
    VerifiableAgentTurnStmt × VerifiableAgentTurnReceipt :=
  let wClean := redactBytes defaultSecretRules wRaw
  let promptRoot := contentCommit256 promptBytes
  let rawRoot := contentCommit256 wRaw
  let cleanRoot := contentCommit256 wClean
  let aud := u1VrfSelectLayer weightRoot boundaryRoots cleanRoot numLayers
  let bIn := boundaryRoots[aud]?.getD ⟨0, by positivity⟩
  let bOut := boundaryRoots[aud + 1]?.getD ⟨0, by positivity⟩
  let chainRoot := u1TurnHead weightRoot promptRoot promptBytes.length
    boundaryRoots u1ProofDigest wRaw.length rawRoot
  let stmt : VerifiableAgentTurnStmt :=
    { weightRoot := weightRoot
      promptLength := promptBytes.length
      promptRoot := promptRoot
      numLayers := numLayers
      turnChainRoot := chainRoot
      rawLength := wRaw.length
      rawRoot := rawRoot
      cleanLength := wClean.length
      cleanRoot := cleanRoot
      claimedAst := ast }
  let rcpt : VerifiableAgentTurnReceipt :=
    { promptBytes := promptBytes
      boundaryRoots := boundaryRoots
      auditedLayer := aud
      auditedBInRoot := bIn
      auditedBOutRoot := bOut
      u1ProofDigest := u1ProofDigest
      wRaw := wRaw
      wClean := wClean
      ruleIndices := rs.map miniJsonCfg.rules.idxOf }
  (stmt, rcpt)

/-- **Symbolic Honest Completeness (`verifyAgentTurnBytes_complete`):**
Any valid prompt, `(L + 1)`-boundary trace, raw CoT output `wRaw`, and valid `miniJsonCfg`
attributed replay `rs` on `redactBytes defaultSecretRules wRaw` encodes to `(stmtBytes, receiptBytes)`
accepted by `verifyAgentTurnBytes` AND inhabiting `CommitsAgentTurnChain` (without unfolding Keccak-f!). -/
theorem verifyAgentTurnBytes_complete
    (weightRoot : Digest256) (promptBytes : List UInt8)
    (numLayers : Nat) (boundaryRoots : List Digest256) (u1ProofDigest : Digest256)
    (wRaw : List UInt8) (rs : List (AttrRule UInt8 MiniNT MiniOp)) (ast : MiniValue)
    (hLpos : 0 < numLayers)
    (hbLen : boundaryRoots.length = numLayers + 1)
    (hrep : AttrReplay miniJsonCfg rs (redactBytes defaultSecretRules wRaw) ast) :
    let (stmt, rcpt) := buildHonestAgentTurn weightRoot promptBytes numLayers
      boundaryRoots u1ProofDigest wRaw rs ast
    verifyAgentTurnBytes (encodeTurnStmt stmt) (encodeTurnReceipt rcpt) = true ∧
    CommitsAgentTurnChain stmt promptBytes boundaryRoots u1ProofDigest wRaw
      (redactBytes defaultSecretRules wRaw) := by
  dsimp only [buildHonestAgentTurn]
  have haLt : u1VrfSelectLayer weightRoot boundaryRoots
      (contentCommit256 (redactBytes defaultSecretRules wRaw)) numLayers < numLayers :=
    u1VrfSelectLayer_lt _ _ _ hLpos
  have haLt1 : u1VrfSelectLayer weightRoot boundaryRoots
      (contentCommit256 (redactBytes defaultSecretRules wRaw)) numLayers < boundaryRoots.length := by
    omega
  have hres : resolveRuleIndices miniJsonCfg.rules (rs.map miniJsonCfg.rules.idxOf) = some rs :=
    resolveRuleIndices_map_idxOf miniJsonCfg.rules rs
      (attrStackReplay_rules_mem hrep)
  have hexec : execAttrReplay miniJsonCfg rs (redactBytes defaultSecretRules wRaw) = some ast :=
    (execAttrReplay_iff miniJsonCfg rs _ ast).mpr hrep
  refine ⟨?_, ?_⟩
  · simp [verifyAgentTurnBytes, decodeTurnStmt_encodeTurnStmt, decodeTurnReceipt_encodeTurnReceipt,
      verifyAgentTurn, verifyAgentTurnWithCfg, hLpos, hbLen, haLt,
      List.getElem?_eq_getElem haLt1,
      miniJsonCfg_is_ll1, defaultSecretRules_allSafe, hres, hexec]
  · refine ⟨rfl, by simp, rfl, rfl, by simp, rfl, by simp⟩

/-- Concrete raw CoT JSON witness matching the live 24-layer `Qwen3.5-0.8B` output byte-for-byte. -/
def sampleQwenTurnRaw : List UInt8 :=
  asciiBytes "{\"cot\":\"Key sk-proj-demo01 on db_stage\",\"tool\":\"audit_cfg\",\"target\":\"db_stage\",\"amount\":64}"

def sampleQwenTurnClean : List UInt8 :=
  asciiBytes "{\"cot\":\"Key [REDACTED_API_KEY] on db_stage\",\"tool\":\"audit_cfg\",\"target\":\"db_stage\",\"amount\":64}"

def sampleQwenTurnAst : MiniValue :=
  .vCotToolCall
    (asciiBytes "Key [REDACTED_API_KEY] on db_stage")
    (asciiBytes "audit_cfg")
    (asciiBytes "db_stage")
    64

def sampleQwenTurnRules : List (AttrRule UInt8 MiniNT MiniOp) :=
  match ll1Parse miniJsonCfg sampleQwenTurnClean with
  | some (rs, _) => rs
  | none => []

set_option maxRecDepth 30000 in
/-- **Joint Premise Inhabitation (`verifyAgentTurnBytes_premises_inhabited`):**
Constructively inhabits all premises of `verifyAgentTurnBytes_sound_or_collision` on a 24-layer
(`25`-boundary) agent turn whose raw CoT carries an inline `sk-proj-demo01` secret (`wClean ≠ wRaw`)
scrubbed to `[REDACTED_API_KEY]` and parsed into `.vCotToolCall`. -/
theorem verifyAgentTurnBytes_premises_inhabited :
    ∃ (stmtBytes receiptBytes : List UInt8) (stmt : VerifiableAgentTurnStmt)
      (promptBytes : List UInt8) (boundaryRoots : List Digest256)
      (u1ProofDigest : Digest256) (wRaw wClean : List UInt8),
      verifyAgentTurnBytes stmtBytes receiptBytes = true ∧
      decodeTurnStmt stmtBytes = some stmt ∧
      CommitsAgentTurnChain stmt promptBytes boundaryRoots u1ProofDigest wRaw wClean ∧
      wRaw ≠ wClean ∧
      stmt.claimedAst = sampleQwenTurnAst := by
  have hred : redactBytes defaultSecretRules sampleQwenTurnRaw = sampleQwenTurnClean := by decide
  have hrepClean : AttrReplay miniJsonCfg sampleQwenTurnRules sampleQwenTurnClean sampleQwenTurnAst := by
    rw [← execAttrReplay_iff]; decide
  have hrep : AttrReplay miniJsonCfg sampleQwenTurnRules
      (redactBytes defaultSecretRules sampleQwenTurnRaw) sampleQwenTurnAst := by
    rwa [hred]
  let zD : Digest256 := ⟨0, by positivity⟩
  let bnds : List Digest256 := List.replicate 25 zD
  let pBytes : List UInt8 := asciiBytes "KEY=sk-proj-9f8a7b6c5d4e TARGET=vault_prod AMT=64"
  let pair := buildHonestAgentTurn zD pBytes 24 bnds zD
    sampleQwenTurnRaw sampleQwenTurnRules sampleQwenTurnAst
  have hcomp := verifyAgentTurnBytes_complete zD pBytes 24 bnds zD
    sampleQwenTurnRaw sampleQwenTurnRules sampleQwenTurnAst
    (by decide) (by decide) hrep
  have hne : sampleQwenTurnRaw ≠ redactBytes defaultSecretRules sampleQwenTurnRaw := by
    rw [hred]; decide
  exact ⟨encodeTurnStmt pair.1, encodeTurnReceipt pair.2, pair.1,
    pBytes, bnds, zD, sampleQwenTurnRaw, redactBytes defaultSecretRules sampleQwenTurnRaw,
    hcomp.1, decodeTurnStmt_encodeTurnStmt pair.1, hcomp.2, hne, rfl⟩

/-- Concrete query-log environment over `[sampleQwenTurnRaw, sampleQwenTurnClean]` (`91` B & `95` B,
both `> 33` B): avoids `unrestrictedEnv` 33-byte pigeonhole and satisfies `BindSound` at `bindAdv = 0 < 1`! -/
@[reducible] def loggedSampleTurnEnv : QueryEnv UInt8 where
  Coins := fun _ => Unit
  Log := List (List UInt8)
  coinsFintype := fun _ => inferInstance
  coinsNonempty := fun _ => ⟨()⟩
  ValidLog := fun _ log => log () = [sampleQwenTurnRaw, sampleQwenTurnClean]
  Grounded := fun l w => w ∈ l

theorem loggedSampleTurnEnv_bindSound :
    BindSound loggedSampleTurnEnv (lengthRootScheme (fun _ => 0) (fun _ => le_rfl)) := by
  intro q log hlog w₁ w₂
  have hfalse : ∀ ω : loggedSampleTurnEnv.Coins q,
      ¬ (loggedSampleTurnEnv.Grounded (log ω) (w₁ ω) ∧
          loggedSampleTurnEnv.Grounded (log ω) (w₂ ω) ∧
          (lengthRootScheme (fun _ => 0) (fun _ => le_rfl)).commit (w₁ ω) =
            (lengthRootScheme (fun _ => 0) (fun _ => le_rfl)).commit (w₂ ω) ∧
          w₁ ω ≠ w₂ ω) := by
    rintro ⟨⟩ ⟨h₁, h₂, hcomm, hne⟩
    change w₁ () ∈ log () at h₁
    change w₂ () ∈ log () at h₂
    rw [hlog] at h₁ h₂
    have hlen : (w₁ ()).length = (w₂ ()).length := congrArg Prod.fst hcomm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h₁ h₂
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    · exact hne (h₁.trans h₂.symm)
    · rw [h₁, h₂] at hlen; exact absurd hlen (by decide)
    · rw [h₁, h₂] at hlen; exact absurd hlen (by decide)
    · exact hne (h₁.trans h₂.symm)
  rw [prob_eq_zero_of_false hfalse]
  exact le_rfl

private theorem buildHonestAgentTurn_raw_fields
    (weightRoot : Digest256) (promptBytes : List UInt8)
    (numLayers : Nat) (boundaryRoots : List Digest256) (u1ProofDigest : Digest256)
    (wRaw : List UInt8) (rs : List (AttrRule UInt8 MiniNT MiniOp)) (ast : MiniValue) :
    let p := buildHonestAgentTurn weightRoot promptBytes numLayers
      boundaryRoots u1ProofDigest wRaw rs ast
    p.1.rawLength = wRaw.length ∧
    ofDigest256 p.1.rawRoot = contentCommit wRaw ∧
    p.2.wRaw = wRaw :=
  ⟨rfl, ofDigest256_contentCommit256 wRaw, rfl⟩

set_option maxRecDepth 30000 in
/-- **Non-Vacuous `< 1` Joint Inhabitation of `verifiableAgentTurn_produced_weld`:**
On `loggedSampleTurnEnv` (`91`-byte `sampleQwenTurnRaw` + `95`-byte `sampleQwenTurnClean`),
ALL THREE premises `(ProducedSound, CertSound, BindSound)` of `verifiableAgentTurn_produced_weld`
hold simultaneously over `lengthRootScheme` at **`ε_u1 = 0`, `ε_cert = 0`, `bindAdv = 0` (`0 + 0 + 0 = 0 < 1`)**,
AND the welded byte-verifier accepts the honest 24-layer `VAGENT01` receipt! -/
theorem verifiableAgentTurn_produced_weld_nonvacuous :
    ∃ (stmt : VerifiableAgentTurnStmt) (rcptBytes : List UInt8)
      (IsOut : Digest256 → (Nat × Digest) → List UInt8 → Prop)
      (V_u1 : Digest256 → (Nat × Digest) → (Nat × Digest) → Unit → Bool)
      (ext_out : Digest256 → (Nat × Digest) → (Nat × Digest) → Unit → List (List UInt8) → List UInt8),
      let S0 := lengthRootScheme (fun _ => 0) (fun _ => le_rfl)
      let cPrompt := (stmt.promptLength, ofDigest256 stmt.promptRoot)
      let cRaw := (stmt.rawLength, ofDigest256 stmt.rawRoot)
      ProducedSound loggedSampleTurnEnv S0 IsOut V_u1 (fun _ => 0) ∧
      CertSound loggedSampleTurnEnv S0 (verifyTurnBytesAtRaw stmt) (CertifiedSanitizedTurn stmt) (fun _ => 0) ∧
      BindSound loggedSampleTurnEnv S0 ∧
      (V_u1 stmt.weightRoot cPrompt cRaw () &&
       verifyTurnBytesAtRaw stmt cRaw rcptBytes &&
       decide (cRaw = cRaw)) = true ∧
      ∀ (q : Nat)
        (cout cout' : Unit → Nat × Digest)
        (πu1 : Unit → Unit) (πrcpt : Unit → List UInt8)
        (log : Unit → List (List UInt8)),
        loggedSampleTurnEnv.ValidLog q log →
        BindingGame.prob (fun ω =>
          (V_u1 stmt.weightRoot cPrompt (cout ω) (πu1 ω) &&
           verifyTurnBytesAtRaw stmt (cout' ω) (πrcpt ω) &&
           decide (cout ω = cout' ω)) = true ∧
          ¬ (loggedSampleTurnEnv.Grounded (log ω) (ext_out stmt.weightRoot cPrompt (cout ω) (πu1 ω) (log ω)) ∧
              IsOut stmt.weightRoot cPrompt (ext_out stmt.weightRoot cPrompt (cout ω) (πu1 ω) (log ω)) ∧
              CertifiedSanitizedTurn stmt (ext_out stmt.weightRoot cPrompt (cout ω) (πu1 ω) (log ω))))
          ≤ 0 := by
  have hred : redactBytes defaultSecretRules sampleQwenTurnRaw = sampleQwenTurnClean := by decide
  have hrepClean : AttrReplay miniJsonCfg sampleQwenTurnRules sampleQwenTurnClean sampleQwenTurnAst := by
    rw [← execAttrReplay_iff]; decide
  have hrep : AttrReplay miniJsonCfg sampleQwenTurnRules
      (redactBytes defaultSecretRules sampleQwenTurnRaw) sampleQwenTurnAst := by
    rwa [hred]
  let zD : Digest256 := ⟨0, by positivity⟩
  let bnds : List Digest256 := List.replicate 25 zD
  let pBytes : List UInt8 := asciiBytes "KEY=sk-proj-9f8a7b6c5d4e TARGET=vault_prod AMT=64"
  have hfields := buildHonestAgentTurn_raw_fields zD pBytes 24 bnds zD
    sampleQwenTurnRaw sampleQwenTurnRules sampleQwenTurnAst
  have hcomp := verifyAgentTurnBytes_complete zD pBytes 24 bnds zD
    sampleQwenTurnRaw sampleQwenTurnRules sampleQwenTurnAst
    (by decide) (by decide) hrep
  dsimp only at hfields hcomp
  rcases hpair : buildHonestAgentTurn zD pBytes 24 bnds zD
      sampleQwenTurnRaw sampleQwenTurnRules sampleQwenTurnAst with ⟨stmt, rcpt⟩
  rw [hpair] at hfields hcomp
  rcases hfields with ⟨hrLen, hrRoot, hrcptW⟩
  dsimp only at hrLen hrRoot hrcptW hcomp
  let S0 := lengthRootScheme (fun _ => 0) (fun _ => le_rfl)
  let cPrompt : Nat × Digest := (stmt.promptLength, ofDigest256 stmt.promptRoot)
  let cRaw : Nat × Digest := (stmt.rawLength, ofDigest256 stmt.rawRoot)
  have hcRawEq : S0.commit sampleQwenTurnRaw = cRaw :=
    Prod.ext hrLen.symm hrRoot.symm
  have hvAtRaw : verifyTurnBytesAtRaw stmt cRaw (encodeTurnReceipt rcpt) = true := by
    unfold verifyTurnBytesAtRaw
    rw [decide_eq_true (rfl : cRaw = cRaw), Bool.true_and]
    exact hcomp.1
  have hextr : extractTurnRaw cRaw (encodeTurnReceipt rcpt) () = sampleQwenTurnRaw := by
    simp only [extractTurnRaw, decodeTurnReceipt_encodeTurnReceipt, hrcptW]
  have hcertRaw : CertifiedSanitizedTurn stmt sampleQwenTurnRaw := by
    have hd := (verifyTurnBytesAtRaw_sound_det stmt cRaw (encodeTurnReceipt rcpt) ()
      (fun _ => 0) (fun _ => le_rfl) hvAtRaw).2
    rwa [hextr] at hd
  let IsOut : Digest256 → (Nat × Digest) → List UInt8 → Prop :=
    fun m cin out => m = stmt.weightRoot ∧ cin = cPrompt ∧ out = sampleQwenTurnRaw
  let V_u1 : Digest256 → (Nat × Digest) → (Nat × Digest) → Unit → Bool :=
    fun m cin cout _ => decide (m = stmt.weightRoot ∧ cin = cPrompt ∧ cout = cRaw)
  have hu1 : ProducedSound loggedSampleTurnEnv S0 IsOut V_u1 (fun _ => 0) := by
    refine ⟨fun _ _ _ _ _ => sampleQwenTurnRaw, fun q m cin cout _ log hlog => ?_⟩
    have hfalse : ∀ ω : loggedSampleTurnEnv.Coins q,
        ¬ (V_u1 (m ω) (cin ω) (cout ω) () = true ∧
            ¬ (loggedSampleTurnEnv.Grounded (log ω) sampleQwenTurnRaw ∧
                IsOut (m ω) (cin ω) sampleQwenTurnRaw ∧
                S0.commit sampleQwenTurnRaw = cout ω)) := by
      rintro ⟨⟩ ⟨hv, hbad⟩
      simp only [V_u1, decide_eq_true_eq] at hv
      have hmem : sampleQwenTurnRaw ∈ log () := by rw [hlog]; exact List.mem_cons_self ..
      exact hbad ⟨hmem, ⟨hv.1, hv.2.1, rfl⟩, hcRawEq.trans hv.2.2.symm⟩
    rw [prob_eq_zero_of_false hfalse]
  have hcert : CertSound loggedSampleTurnEnv S0 (verifyTurnBytesAtRaw stmt)
      (CertifiedSanitizedTurn stmt) (fun _ => 0) := by
    refine ⟨fun _ _ _ => sampleQwenTurnRaw, fun q c π log hlog => ?_⟩
    have hfalse : ∀ ω : loggedSampleTurnEnv.Coins q,
        ¬ (verifyTurnBytesAtRaw stmt (c ω) (π ω) = true ∧
            ¬ (loggedSampleTurnEnv.Grounded (log ω) sampleQwenTurnRaw ∧
                S0.commit sampleQwenTurnRaw = c ω ∧
                CertifiedSanitizedTurn stmt sampleQwenTurnRaw)) := by
      rintro ⟨⟩ ⟨hv, hbad⟩
      unfold verifyTurnBytesAtRaw at hv
      rw [Bool.and_eq_true, decide_eq_true_eq] at hv
      have hmem : sampleQwenTurnRaw ∈ log () := by rw [hlog]; exact List.mem_cons_self ..
      exact hbad ⟨hmem, hcRawEq.trans hv.1.symm, hcertRaw⟩
    rw [prob_eq_zero_of_false hfalse]
  rcases verifiableAgentTurn_produced_weld loggedSampleTurnEnv stmt
      (fun _ => 0) (fun _ => 0) (fun _ => le_rfl) hu1 hcert loggedSampleTurnEnv_bindSound
      with ⟨ext_out, hweld⟩
  refine ⟨stmt, encodeTurnReceipt rcpt, IsOut, V_u1, ext_out, hu1, hcert,
    loggedSampleTurnEnv_bindSound, ?_, ?_⟩
  · dsimp only [V_u1]
    rw [decide_eq_true ⟨rfl, rfl, rfl⟩, Bool.true_and, hvAtRaw, Bool.true_and]
    exact decide_eq_true rfl
  · intro q cout cout' πu1 πrcpt log hlog
    have hb := hweld q cout cout' πu1 πrcpt log hlog
    exact le_trans hb (by norm_num)

/-- **Falsifier 1a (Prompt Length Mismatch Rejected Unconditionally):**
Any receipt whose `promptBytes.length ≠ stmt.promptLength` is rejected (`= false`) unconditionally. -/
theorem tk_prompt_length_mismatch_refused
    (stmt : VerifiableAgentTurnStmt) (rcpt : VerifiableAgentTurnReceipt)
    (hlen : rcpt.promptBytes.length ≠ stmt.promptLength) :
    verifyAgentTurnBytes (encodeTurnStmt stmt) (encodeTurnReceipt rcpt) = false := by
  unfold verifyAgentTurnBytes
  rw [decodeTurnStmt_encodeTurnStmt, decodeTurnReceipt_encodeTurnReceipt]
  dsimp only
  unfold verifyAgentTurn verifyAgentTurnWithCfg
  simp [hlen]

/-- **Falsifier 1b (`TK` Equal-Length Prompt Splice Refused or Input-Pinned `DenseCollision`):**
Any receipt with `rcpt.promptBytes ≠ namedPrompt` against `(stmt.promptLength, stmt.promptRoot)`
is either rejected (`= false`) or collides at the input-pinned `DenseCollision` frames. -/
theorem tk_prompt_mismatch_falsifier
    (stmt : VerifiableAgentTurnStmt) (rcpt : VerifiableAgentTurnReceipt)
    (namedPrompt : List UInt8)
    (hnpLen : namedPrompt.length = stmt.promptLength)
    (hnpRoot : contentCommit namedPrompt = ofDigest256 stmt.promptRoot)
    (hdiff : rcpt.promptBytes ≠ namedPrompt) :
    verifyAgentTurnBytes (encodeTurnStmt stmt) (encodeTurnReceipt rcpt) = false ∨
    DenseCollision (rcpt.promptBytes.map UInt8.toNat) (namedPrompt.map UInt8.toNat) := by
  cases hver : verifyAgentTurnBytes (encodeTurnStmt stmt) (encodeTurnReceipt rcpt) with
  | false => exact Or.inl rfl
  | true =>
      right
      unfold verifyAgentTurnBytes at hver
      rw [decodeTurnStmt_encodeTurnStmt, decodeTurnReceipt_encodeTurnReceipt] at hver
      dsimp only at hver
      unfold verifyAgentTurn verifyAgentTurnWithCfg at hver
      cases hres : resolveRuleIndices miniJsonCfg.rules rcpt.ruleIndices with
      | none => simp [hres] at hver
      | some rs =>
          rw [hres] at hver
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hver
          rcases hver with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩,
            hpLen⟩, hpRoot⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩
          rcases contentCommit_eq_or_denseCollision
              (hpLen.trans hnpLen.symm) (hpRoot.trans hnpRoot.symm) with heq | hcol
          · exact False.elim (hdiff heq)
          · exact hcol

/-- **Falsifier 2 (`TK` Intermediate Boundary Splice Refused or Input-Pinned `U1TurnHeadCollision`):**
Splicing ANY intermediate layer boundary (`rcpt.boundaryRoots ≠ namedBoundaries`) against a fixed
`stmt` either rejects (`= false`) or collides at the input-pinned `U1TurnHeadCollision` frames. -/
theorem tk_boundary_mismatch_falsifier
    (stmt : VerifiableAgentTurnStmt) (rcpt : VerifiableAgentTurnReceipt)
    (namedBoundaries : List Digest256) (namedProofDigest : Digest256)
    (hnturn : u1TurnHead stmt.weightRoot stmt.promptRoot stmt.promptLength
      namedBoundaries namedProofDigest stmt.rawLength stmt.rawRoot = stmt.turnChainRoot)
    (hdiff : rcpt.boundaryRoots ≠ namedBoundaries) :
    verifyAgentTurnBytes (encodeTurnStmt stmt) (encodeTurnReceipt rcpt) = false ∨
    U1TurnHeadCollision
      stmt.weightRoot stmt.promptRoot stmt.promptLength
      rcpt.boundaryRoots rcpt.u1ProofDigest stmt.rawLength stmt.rawRoot
      stmt.weightRoot stmt.promptRoot stmt.promptLength
      namedBoundaries namedProofDigest stmt.rawLength stmt.rawRoot := by
  cases hver : verifyAgentTurnBytes (encodeTurnStmt stmt) (encodeTurnReceipt rcpt) with
  | false => exact Or.inl rfl
  | true =>
      right
      unfold verifyAgentTurnBytes at hver
      rw [decodeTurnStmt_encodeTurnStmt, decodeTurnReceipt_encodeTurnReceipt] at hver
      dsimp only at hver
      unfold verifyAgentTurn verifyAgentTurnWithCfg at hver
      cases hres : resolveRuleIndices miniJsonCfg.rules rcpt.ruleIndices with
      | none => simp [hres] at hver
      | some rs =>
          rw [hres] at hver
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hver
          rcases hver with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩,
            _⟩, _⟩, hturn⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩
          rcases u1TurnHead_eq_or_collision
              stmt.weightRoot stmt.promptRoot stmt.promptLength
              rcpt.boundaryRoots rcpt.u1ProofDigest stmt.rawLength stmt.rawRoot
              stmt.weightRoot stmt.promptRoot stmt.promptLength
              namedBoundaries namedProofDigest stmt.rawLength stmt.rawRoot
              (hturn.trans hnturn.symm) with ⟨_, _, _, hbEq, _, _, _⟩ | hcol
          · exact False.elim (hdiff hbEq)
          · exact hcol

/-- **Falsifier 3a (Universal Secret-Bearing `wClean` Rejection):**
For **every** `stmt`, **every** `rcpt` (regardless of `rcpt.wRaw`), and **every** `rt ∈ defaultSecretRules`,
if `¬ AbsentPlain rcpt.wClean rt.pat`, then `verifyAgentTurnBytes` rejects (`= false`) unconditionally! -/
theorem dirty_clean_bytes_refused
    (stmt : VerifiableAgentTurnStmt) (rcpt : VerifiableAgentTurnReceipt)
    (rt : RedactRule UInt8) (hrt : rt ∈ defaultSecretRules)
    (hdirty : ¬ AbsentPlain rcpt.wClean rt.pat) :
    verifyAgentTurnBytes (encodeTurnStmt stmt) (encodeTurnReceipt rcpt) = false := by
  cases hver : verifyAgentTurnBytes (encodeTurnStmt stmt) (encodeTurnReceipt rcpt) with
  | false => rfl
  | true =>
      exfalso
      unfold verifyAgentTurnBytes at hver
      rw [decodeTurnStmt_encodeTurnStmt, decodeTurnReceipt_encodeTurnReceipt] at hver
      dsimp only at hver
      unfold verifyAgentTurn verifyAgentTurnWithCfg at hver
      cases hres : resolveRuleIndices miniJsonCfg.rules rcpt.ruleIndices with
      | none => simp [hres] at hver
      | some rs =>
          rw [hres] at hver
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hver
          rcases hver with ⟨⟨_, hred⟩, _⟩
          have habs := (redactBytes_scrubs_padded_complement defaultSecretRules
            defaultSecretRules_allSafe rt hrt rcpt.wRaw).1
          rw [← hred] at habs
          exact hdirty habs

set_option maxRecDepth 30000 in
/-- **Falsifier 3b (Unredacted `sampleQwenTurnRaw` Rejected for EVERY `rcpt.wRaw`):**
Supplying unredacted `sampleQwenTurnRaw` (`"sk-proj-demo01"`) as `rcpt.wClean` fails `verifyAgentTurnBytes`
unconditionally for **every** `stmt` and **every** `rcpt` (without restricting `rcpt.wRaw`)! -/
theorem unredacted_cot_secret_falsifier
    (stmt : VerifiableAgentTurnStmt) (rcpt : VerifiableAgentTurnReceipt)
    (hclean : rcpt.wClean = sampleQwenTurnRaw) :
    verifyAgentTurnBytes (encodeTurnStmt stmt) (encodeTurnReceipt rcpt) = false := by
  let skRule : RedactRule UInt8 :=
    ⟨"api_key", asciiBytes "sk-", isApiKeyBodyByte, asciiBytes "[REDACTED_API_KEY]"⟩
  have hmem : skRule ∈ defaultSecretRules := List.mem_cons_self ..
  have hnotAbsW : ¬ AbsentW sampleQwenTurnRaw skRule.pat := by decide
  have hnotPlain : ¬ AbsentPlain rcpt.wClean skRule.pat := by
    rw [hclean, ← Minidregg.Compiler.PolicyAstTransducerEmit.absentW_iff_plain]
    exact hnotAbsW
  exact dirty_clean_bytes_refused stmt rcpt skRule hmem hnotPlain

/-- Exhaustive fuel-bounded stack refuter for `miniJsonCfg` (`true` => no `AttrStackReplay` exists). -/
def mustFailStack : Nat → List UInt8 → List (WorkItem UInt8 MiniNT MiniOp) → Bool
  | 0, _, _ => false
  | _ + 1, [], [] => false
  | _ + 1, _ :: _, [] => true
  | _ + 1, [], .sym (.terminal _) :: _ => true
  | fuel + 1, b :: w, .sym (.terminal t) :: cstk =>
      if b = t then mustFailStack fuel w cstk else true
  | fuel + 1, w, .reduce _ _ :: cstk =>
      mustFailStack fuel w cstk
  | fuel + 1, w, .sym (.nonterminal A) :: cstk =>
      miniJsonCfg.rules.all fun r =>
        if r.lhs = A then
          mustFailStack fuel w (r.rhs.map .sym ++ .reduce r.op r.rhs.length :: cstk)
        else true

private theorem mustFailStack_sound :
    ∀ (fuel : Nat) {rs : List (AttrRule UInt8 MiniNT MiniOp)}
      {w : List UInt8} {cstk : List (WorkItem UInt8 MiniNT MiniOp)}
      {vstk : List MiniValue} {ast : MiniValue},
      AttrStackReplay miniJsonCfg rs w cstk vstk ast →
      mustFailStack fuel w cstk = false := by
  intro fuel
  induction fuel with
  | zero => intros; rfl
  | succ fuel ih =>
      intro rs w cstk vstk ast hrep
      cases hrep with
      | done _ => rfl
      | term _ hnext => simp [mustFailStack, ih hnext]
      | reduce _ _ _ hnext => cases w <;> exact ih hnext
      | @rule r _ _ _ _ _ hr hnext =>
          simp only [mustFailStack, Bool.eq_false_iff, ne_eq, List.all_eq_true]
          intro hall
          have hm := hall r hr
          simp [ih hnext] at hm

/-- Non-triviality of `CertifiedSanitizedTurn`: the empty byte string `[]` never satisfies it. -/
theorem certifiedSanitizedTurn_empty_false (stmt : VerifiableAgentTurnStmt) :
    ¬ CertifiedSanitizedTurn stmt [] := by
  rintro ⟨_, _, _, rs, hrep, _⟩
  have hcleanEmpty : redactBytes defaultSecretRules [] = [] := by decide
  rw [hcleanEmpty] at hrep
  have hf := mustFailStack_sound 10 hrep
  have ht : mustFailStack 10 [] [.sym (.nonterminal miniJsonCfg.initial)] = true := by decide
  exact absurd (hf.symm.trans ht) Bool.false_ne_true

set_option maxRecDepth 60000 in
/-- Kernel-proved impossibility of ANY `AttrReplay` on `ambigSplicePayload` in `miniJsonCfg`. -/
theorem ambigSplicePayload_no_miniJson_replay
    (rs : List (AttrRule UInt8 MiniNT MiniOp)) (ast : MiniValue) :
    ¬ AttrReplay miniJsonCfg rs ambigSplicePayload ast := by
  intro hrep
  have hf := mustFailStack_sound 80 hrep
  have ht : mustFailStack 80 ambigSplicePayload [.sym (.nonterminal miniJsonCfg.initial)] = true := by
    decide
  exact absurd (hf.symm.trans ht) Bool.false_ne_true

/-- **Falsifier 4 (Duplicate-Key JSON Splice Refused Unconditionally on `verifyAgentTurnBytes`):**
1. For **every** `stmt` and **every** `rcpt` (including any forged `rcpt.ruleIndices`!) with
   `rcpt.wClean = ambigSplicePayload`, `verifyAgentTurnBytes (encodeTurnStmt stmt) (encodeTurnReceipt rcpt) = false`!
2. Furthermore, `verifyAgentTurnWithCfg` unconditionally rejects `ambigMiniJsonCfg` (`= false`). -/
theorem duplicate_key_splice_refused
    (stmt : VerifiableAgentTurnStmt) (rcpt : VerifiableAgentTurnReceipt)
    (hsplice : rcpt.wClean = ambigSplicePayload) :
    verifyAgentTurnBytes (encodeTurnStmt stmt) (encodeTurnReceipt rcpt) = false ∧
    verifyAgentTurnWithCfg ambigMiniJsonCfg stmt rcpt = false := by
  refine ⟨?_, ?_⟩
  · cases hver : verifyAgentTurnBytes (encodeTurnStmt stmt) (encodeTurnReceipt rcpt) with
    | false => rfl
    | true =>
        exfalso
        unfold verifyAgentTurnBytes at hver
        rw [decodeTurnStmt_encodeTurnStmt, decodeTurnReceipt_encodeTurnReceipt] at hver
        dsimp only at hver
        unfold verifyAgentTurn verifyAgentTurnWithCfg at hver
        cases hres : resolveRuleIndices miniJsonCfg.rules rcpt.ruleIndices with
        | none => simp [hres] at hver
        | some rs =>
            rw [hres] at hver
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hver
            have hexec := hver.2
            rw [hsplice] at hexec
            have hrep := (execAttrReplay_iff miniJsonCfg rs ambigSplicePayload stmt.claimedAst).mp hexec
            exact ambigSplicePayload_no_miniJson_replay rs stmt.claimedAst hrep
  · have hambig : ll1Deterministic ambigMiniJsonCfg = false := ambigMiniJsonCfg_splice_attack.1
    simp [verifyAgentTurnWithCfg, hambig]

/-! ## §7. Live 24-Layer `Qwen3.5-0.8B` `VASTMT01` / `VAGENT01` Cross-Language `#eval` Check -/

private def hexNibble (c : Char) : Option Nat :=
  let n := c.toNat
  if 0x30 ≤ n ∧ n ≤ 0x39 then some (n - 0x30)
  else if 0x61 ≤ n ∧ n ≤ 0x66 then some (n - 0x61 + 10)
  else if 0x41 ≤ n ∧ n ≤ 0x46 then some (n - 0x41 + 10)
  else none

private def decodeHexChars : List Char → Option (List UInt8)
  | [] => some []
  | hi :: lo :: rest => do
      let h ← hexNibble hi
      let l ← hexNibble lo
      let tail ← decodeHexChars rest
      some (UInt8.ofNat (16 * h + l) :: tail)
  | [_] => none

def mustDecodeHex (s : String) : List UInt8 :=
  (decodeHexChars s.toList).getD []

/-- Exact `236`-byte `VASTMT01` statement emitted by the live 24-layer integer `Qwen3.5-0.8B` agent CLI. -/
def liveQwen35StmtHex : String :=
  "564153544d5430314aa1ef57d119e840c4e848c638027fbc85373fb8bcc2610e4e7c04a4ebc9e30e96ff8beab9071d6766c0e64795a41a280f7f6d1935abd8f0fbaba44a3b1fd5ac8d5018ff54e83b3c1f8d3ad0d4d46c9739ebcadd36a497219ddacd46a5b669cf4c1c46d95bff5ec49615e87f2f585d607e9e09289d87bc3c72d21fcf18e432a4ac7add9df2315fff44ebafea4337c7f55169e3dd79d546e713b733c990b0a19c71d7d2f5941e05a80522ff4b6579205b52454441435445445f4150495f4b45595d206f6e2064625f737461676509ff61756469745f63666708ff64625f737461676540ff"

/-- Exact `1,415`-byte `VAGENT01` receipt emitted by the live 24-layer integer `Qwen3.5-0.8B` agent CLI. -/
def liveQwen35ReceiptHex : String :=
  "564147454e54303196ff20414d543d31300a7b22636f74223a224b657920736b2d70726f6a2d64656d6f3031206f6e2064625f7374616765222c22746f6f6c223a2261756469745f636667222c22746172676574223a2264625f7374616765222c22616d6f756e74223a31307d0a4b45593d736b2d70726f6a2d396638613762366335643465205441524745543d7661756c745f70726f6420414d543d36340a19ff22decdef6148e011dd175981a367d4fddca29e0157a710c5dc2c802f695af937d6e162c4eaae5a56f8bdf21e6ac071c4ccfeaa3c88a6d5498fc1692fc185ccbd886ee8f08098feb23561a77683f2386d3930f1312e2c84f06b653386ac4b5b1c52c456af885c057015a61c0a2f41043fe472b8ccbd832910b1f34488efb33939bd0c08190f2bd921c86928a97aed202e7e6568c9ef158d4ee33d57edcc3561e05f9e7d4a4781f0d7bd48bfe9703d66f974c656345ee784354811518224507a41c7045daf4e22261fb02201baf5e7465341601e7da36734dfd2ee209862ed63cd0826cc2b77e1e36f9faab8a1ad3543b187377205192edad6c82facc8b391fc79416ae2f2eab16db92f617ea26d0c5bc7d79ea845411aa9ea6952e255db7ef8a2e557326c98c2c1eda785e832b86bb33f86d43f757748503eef30d770fcbc27823cf3c4a4cc8cdc15da993d27d43fb04255dac05578c0fc99e61bc172199a974309f96c5b98a2a0b87a02d93d802b95ca4d23c10027c37b308000410477ed2cb580eae28dc18943706d043ebe6854a60ade55490aad012bd72f844e7caebd5d3eed6d3044f2833679da44013f2087824855d36d235a5e518f7dff5bbf46caf4fe3da8c6014bcc5b124e77241df4e7319f527f9de0389aa60d933a4de668a354bfb5c9c0e57b267b7d06cb78f7ec4be292b9a7add7770ce79b4019beca38ae4eb2f36d05a38a8485a03f91a368a2c3c875d21267bb731ce147abcdc626d9960de4e222be16a4d7619c3f23232fea6ca1335528cedb714272cfc9c09230183d79edaa998efac085544bae4f2921aa807c58fff6ef8e918e23d0cd84137ab30c70dc382a8ed947cd8f258b45ac8e2f350840f0b91acf0a44cc2e25b22751b9df442c7df1a74db70883b13e0d5b30d3819eba53d3c1af587c41f2022e51df08e95d8f7872c721a7f1843ba3b787e689cf75a6b4bbfa597a9477ea9d925c211b4622d4fa6da961f404786088df97e808be391ec9225b0992ea5fb94647d8710bf5290c859f5206175de1866bf8ad0d1d45a7611cb74ae003936a078580f0cfeb881a3be25b841b2e4cf2725a42acf764a4c07b0a496d7c6e18b425b0cadad3f2d80c9209ffe557326c98c2c1eda785e832b86bb33f86d43f757748503eef30d770fcbc27823cf3c4a4cc8cdc15da993d27d43fb04255dac05578c0fc99e61bc172199a974373c98e4d9b2aa1b2c78988a53868f97d283abdc7448f10db8bae11b8774a2e115bff7b22636f74223a224b657920736b2d70726f6a2d64656d6f3031206f6e2064625f7374616765222c22746f6f6c223a2261756469745f636667222c22746172676574223a2264625f7374616765222c22616d6f756e74223a36347d5fff7b22636f74223a224b6579205b52454441435445445f4150495f4b45595d206f6e2064625f7374616765222c22746f6f6c223a2261756469745f636667222c22746172676574223a2264625f7374616765222c22616d6f756e74223a36347d52ffff0fff01ff0fff04ff06ff0fff0fff10ff58ff71ff85ff2eff68ff5fff52ff51ff4eff50ff61ff52ff51ff6bff4eff5dff56ff6bff58ff52ff66ff69ff2eff7bff7aff2eff70ff6eff6bff7fff80ff6dff73ff71ff12ff0fff0fff0fff0fff10ff6dff81ff70ff75ff80ff6bff6fff72ff73ff12ff0fff0fff0fff0fff10ff70ff6eff6bff7fff80ff6dff73ff71ff12ff0fff0fff0fff0fff20ff28ff1aff0fff0fff"

def liveQwen35StmtBytes : List UInt8 := mustDecodeHex liveQwen35StmtHex
def liveQwen35ReceiptBytes : List UInt8 := mustDecodeHex liveQwen35ReceiptHex

/-- Build-time `#eval` conformance & negative-vector audit against the live Rust `VAGENT01` bytes. -/
def verifyLiveQwen35Vectors : IO Unit := do
  unless liveQwen35StmtBytes.length == 236 && liveQwen35ReceiptBytes.length == 1415 do
    throw (IO.userError "live VASTMT01/VAGENT01 hex byte length mismatch")
  unless verifyAgentTurnBytes liveQwen35StmtBytes liveQwen35ReceiptBytes do
    throw (IO.userError "verifyAgentTurnBytes rejected live Qwen3.5-0.8B VAGENT01 receipt!")
  let some stmt := decodeTurnStmt liveQwen35StmtBytes
    | throw (IO.userError "decodeTurnStmt failed on liveQwen35StmtBytes")
  let some rcpt := decodeTurnReceipt liveQwen35ReceiptBytes
    | throw (IO.userError "decodeTurnReceipt failed on liveQwen35ReceiptBytes")
  unless encodeTurnStmt stmt == liveQwen35StmtBytes &&
      encodeTurnReceipt rcpt == liveQwen35ReceiptBytes &&
      stmt.numLayers == 24 &&
      stmt.promptLength == 150 &&
      stmt.rawLength == 91 &&
      stmt.cleanLength == 95 &&
      stmt.claimedAst == sampleQwenTurnAst &&
      rcpt.auditedLayer == 9 &&
      rcpt.boundaryRoots.length == 25 &&
      rcpt.wRaw == sampleQwenTurnRaw &&
      rcpt.wClean == sampleQwenTurnClean do
    throw (IO.userError "decoded live Qwen3.5-0.8B statement/receipt field mismatch")

  -- Cross-check live wire falsifiers in Lean executable path:
  let badPromptRcpt := { rcpt with promptBytes := rcpt.promptBytes.set 0 0xFF }
  let badBoundaryRcpt := { rcpt with boundaryRoots := rcpt.boundaryRoots.set 3 ⟨1, by decide⟩ }
  let trailingRcptBytes := liveQwen35ReceiptBytes ++ [0x00]
  unless !verifyAgentTurnBytes liveQwen35StmtBytes (encodeTurnReceipt badPromptRcpt) &&
      !verifyAgentTurnBytes liveQwen35StmtBytes (encodeTurnReceipt badBoundaryRcpt) &&
      !verifyAgentTurnBytes liveQwen35StmtBytes trailingRcptBytes &&
      (StreamCodec.nat.toLawful.decode [0, 255]).isNone do
    throw (IO.userError "live VAGENT01 falsifier unexpectedly accepted!")

  -- Also cross-check on-disk golden vector files in `formal_weld/vectors/`:
  let stmtPath : System.FilePath :=
    "/Users/ember/dev/zkml-research/research/afp_and_unified_wave_2026_11_21/formal_weld/vectors/vagent01_stmt.bin"
  let rcptPath : System.FilePath :=
    "/Users/ember/dev/zkml-research/research/afp_and_unified_wave_2026_11_21/formal_weld/vectors/vagent01_receipt.bin"
  if (← stmtPath.pathExists) && (← rcptPath.pathExists) then
    let diskStmt := (← IO.FS.readBinFile stmtPath).toList
    let diskRcpt := (← IO.FS.readBinFile rcptPath).toList
    unless diskStmt == liveQwen35StmtBytes && diskRcpt == liveQwen35ReceiptBytes do
      throw (IO.userError "on-disk VASTMT01/VAGENT01 vector differs from Lean embedded bytes!")

  -- When `VAGENT01_VERIFY_DIR` is set (e.g. from `build_and_verify.sh` after live CLI run),
  -- verify the freshly generated ZK-blinded `VASTMT01` + `VAGENT01` wire files directly in Lean!
  if let some liveDir ← IO.getEnv "VAGENT01_VERIFY_DIR" then
    let freshStmtPath : System.FilePath := System.FilePath.mk liveDir / "vagent01_stmt.bin"
    let freshRcptPath : System.FilePath := System.FilePath.mk liveDir / "vagent01_receipt.bin"
    let freshStmtBytes := (← IO.FS.readBinFile freshStmtPath).toList
    let freshRcptBytes := (← IO.FS.readBinFile freshRcptPath).toList
    unless verifyAgentTurnBytes freshStmtBytes freshRcptBytes do
      throw (IO.userError "Lean verifyAgentTurnBytes rejected freshly emitted Rust VAGENT01 bytes!")
    let some fStmt := decodeTurnStmt freshStmtBytes
      | throw (IO.userError "Lean decodeTurnStmt failed on fresh VASTMT01 bytes")
    let some fRcpt := decodeTurnReceipt freshRcptBytes
      | throw (IO.userError "Lean decodeTurnReceipt failed on fresh VAGENT01 bytes")
    unless fStmt.weightRoot == stmt.weightRoot &&
        fStmt.promptLength == stmt.promptLength &&
        fStmt.promptRoot == stmt.promptRoot &&
        fStmt.numLayers == 24 &&
        fStmt.rawLength == 91 &&
        fStmt.rawRoot == stmt.rawRoot &&
        fStmt.cleanLength == 95 &&
        fStmt.cleanRoot == stmt.cleanRoot &&
        fStmt.claimedAst == sampleQwenTurnAst &&
        fRcpt.wRaw == sampleQwenTurnRaw &&
        fRcpt.wClean == sampleQwenTurnClean do
      throw (IO.userError "freshly emitted deterministic VASTMT01/VAGENT01 fields diverged!")

#eval verifyLiveQwen35Vectors

/-! ## §8. Axiom Audit (`#guard_msgs` Pins) -/

/-- info: 'Minidregg.Assurance.VerifiableAgentTurnWeld.decodeTurnStmt_encodeTurnStmt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decodeTurnStmt_encodeTurnStmt
/-- info: 'Minidregg.Assurance.VerifiableAgentTurnWeld.encodeTurnStmt_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms encodeTurnStmt_injective
/-- info: 'Minidregg.Assurance.VerifiableAgentTurnWeld.trailing_stmt_bytes_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms trailing_stmt_bytes_refused
/-- info: 'Minidregg.Assurance.VerifiableAgentTurnWeld.decodeTurnReceipt_encodeTurnReceipt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decodeTurnReceipt_encodeTurnReceipt
/-- info: 'Minidregg.Assurance.VerifiableAgentTurnWeld.encodeTurnReceipt_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms encodeTurnReceipt_injective
/-- info: 'Minidregg.Assurance.VerifiableAgentTurnWeld.trailing_wire_bytes_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms trailing_wire_bytes_refused
/-- info: 'Minidregg.Assurance.VerifiableAgentTurnWeld.u1TurnHead_eq_or_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms u1TurnHead_eq_or_collision
/-- info: 'Minidregg.Assurance.VerifiableAgentTurnWeld.verifyAgentTurnBytes_sound_or_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms verifyAgentTurnBytes_sound_or_collision
/-- info: 'Minidregg.Assurance.VerifiableAgentTurnWeld.verifyAgentTurnBytes_certSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms verifyAgentTurnBytes_certSound
/-- info: 'Minidregg.Assurance.VerifiableAgentTurnWeld.verifiableAgentTurn_produced_weld' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms verifiableAgentTurn_produced_weld
/-- info: 'Minidregg.Assurance.VerifiableAgentTurnWeld.verifiableAgentTurn_produced_weld_of_grounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms verifiableAgentTurn_produced_weld_of_grounded
/-- info: 'Minidregg.Assurance.VerifiableAgentTurnWeld.loggedSampleTurnEnv_bindSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms loggedSampleTurnEnv_bindSound
/-- info: 'Minidregg.Assurance.VerifiableAgentTurnWeld.verifiableAgentTurn_produced_weld_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms verifiableAgentTurn_produced_weld_nonvacuous
/-- info: 'Minidregg.Assurance.VerifiableAgentTurnWeld.certifiedSanitizedTurn_empty_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certifiedSanitizedTurn_empty_false
/-- info: 'Minidregg.Assurance.VerifiableAgentTurnWeld.verifyAgentTurnBytes_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms verifyAgentTurnBytes_complete
/-- info: 'Minidregg.Assurance.VerifiableAgentTurnWeld.verifyAgentTurnBytes_premises_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms verifyAgentTurnBytes_premises_inhabited
/-- info: 'Minidregg.Assurance.VerifiableAgentTurnWeld.tk_prompt_length_mismatch_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tk_prompt_length_mismatch_refused
/-- info: 'Minidregg.Assurance.VerifiableAgentTurnWeld.tk_prompt_mismatch_falsifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tk_prompt_mismatch_falsifier
/-- info: 'Minidregg.Assurance.VerifiableAgentTurnWeld.tk_boundary_mismatch_falsifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tk_boundary_mismatch_falsifier
/-- info: 'Minidregg.Assurance.VerifiableAgentTurnWeld.dirty_clean_bytes_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dirty_clean_bytes_refused
/-- info: 'Minidregg.Assurance.VerifiableAgentTurnWeld.unredacted_cot_secret_falsifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms unredacted_cot_secret_falsifier
/-- info: 'Minidregg.Assurance.VerifiableAgentTurnWeld.ambigSplicePayload_no_miniJson_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ambigSplicePayload_no_miniJson_replay
/-- info: 'Minidregg.Assurance.VerifiableAgentTurnWeld.duplicate_key_splice_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms duplicate_key_splice_refused

end Minidregg.Assurance.VerifiableAgentTurnWeld
