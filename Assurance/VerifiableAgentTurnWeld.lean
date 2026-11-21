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

- **`decodeTurnStmt_encodeTurnStmt`, `encodeTurnStmt_injective`,
  `decodeTurnReceipt_encodeTurnReceipt`, `encodeTurnReceipt_injective`:**
  Canonical `StreamCodec` round-trip, injectivity, and trailing-byte refusal on `VASTMT01` & `VAGENT01`.
- **`u1TurnHead_eq_or_collision`:**
  Full inductive `cSHAKE256` hash-chain collision extraction: two boundary chains producing the same
  32-byte `turnChainRoot` agree on `weightRoot`, `promptLength`, `promptRoot`, every intermediate
  layer boundary `boundaryRoots[0 .. L]`, `u1ProofDigest`, `rawLength`, and `rawRoot` — or exhibit
  an explicit `FramedXofCollision cshakeC`.
- **`verifyAgentTurnBytes_sound_or_collision`:**
  End-to-end byte-verifier soundness welding canonical wire decoding, `U1` boundary-chain commitment,
  `wClean = redactBytes defaultSecretRules wRaw` + universal `Regex.paddedComplement` secret absence,
  and unique LL(1) `MiniValue` AST extraction, up to explicit `FramedXofCollision cshakeC`.
- **`verifiableAgentTurn_produced_and_cert_weld`:**
  Query-indexed straightline composition instantiating `CertificateComposition.cert_produced_weld`
  (`P8`) + `CertificateComposition.cert_and` (`P5`).
- **Premise inhabitation, `TK` prompt/boundary mismatch falsifiers, unredacted CoT rejection,
  duplicate-key JSON splice refusal, and `#eval` cross-verification on live 24-layer `Qwen3.5-0.8B`
  `VASTMT01` (`236 B`) & `VAGENT01` (`1,415 B`) wire bytes.**
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
open Minidregg.Compiler.Tower256ContentCert (contentCommit DenseCollision)
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

private theorem list_snoc_of_ne_nil {α : Type} (xs : List α) (hne : xs ≠ []) :
    ∃ pre last, xs = pre ++ [last] := by
  induction xs with
  | nil => exact False.elim (hne rfl)
  | cons x rest ih =>
      by_cases hr : rest = []
      · exact ⟨[], x, by simp [hr]⟩
      · rcases ih hr with ⟨pre, last, rfl⟩
        exact ⟨x :: pre, last, rfl⟩

/-- Inductive unrolling of `u1ChainFold`: equal chain roots over equal-length boundary lists either
force identical `(weightRoot, promptLen, promptRoot, boundaryRoots)` or expose a `FramedXofCollision`. -/
theorem u1ChainFold_eq_or_collision
    (w₁ p₁ : Digest256) (pl₁ : Nat) (bs₁ : List Digest256)
    (w₂ p₂ : Digest256) (pl₂ : Nat) (bs₂ : List Digest256)
    (hlen : bs₁.length = bs₂.length)
    (hchain : u1ChainFold w₁ p₁ pl₁ bs₁ = u1ChainFold w₂ p₂ pl₂ bs₂) :
    (w₁ = w₂ ∧ pl₁ = pl₂ ∧ p₁ = p₂ ∧ bs₁ = bs₂) ∨
    ∃ cust left right, FramedXofCollision cshakeC cust left right := by
  induction bs₁ using List.reverseRecOn generalizing bs₂ with
  | nil =>
      have hbs₂ : bs₂ = [] := List.eq_nil_of_length_eq_zero hlen.symm
      subst hbs₂
      simp only [u1ChainFold, u1StepLoop, u1InitAcc] at hchain
      rcases cshake256D256_eq_or_collision _ _ _ hchain with hfr | hcol
      · have hinj := streamCodec_encode_injective u1StepFrameCodec hfr
        simp only [Prod.mk.injEq, true_and] at hinj
        exact Or.inl ⟨hinj.1, hinj.2.1, hinj.2.2, rfl⟩
      · exact Or.inr ⟨_, _, _, hcol⟩
  | append_singleton pre₁ last₁ ih =>
      have hne₂ : bs₂ ≠ [] := by
        intro hnil
        rw [hnil] at hlen
        simp at hlen
      rcases list_snoc_of_ne_nil bs₂ hne₂ with ⟨pre₂, last₂, rfl⟩
      have hpreLen : pre₁.length = pre₂.length := by
        simp only [List.length_append, List.length_singleton] at hlen
        omega
      simp only [u1ChainFold, u1StepLoop_append_singleton, Nat.zero_add, u1StepAcc] at hchain
      rcases cshake256D256_eq_or_collision _ _ _ hchain with hfr | hcol
      · have hinj := streamCodec_encode_injective u1StepFrameCodec hfr
        simp only [Prod.mk.injEq, true_and] at hinj
        rcases hinj with ⟨hacc, _, hlast⟩
        subst hlast
        rcases ih pre₂ hpreLen hacc with ⟨hw, hpl, hp, hpre⟩ | hcolPre
        · exact Or.inl ⟨hw, hpl, hp, congrArg (· ++ [last₁]) hpre⟩
        · exact Or.inr hcolPre
      · exact Or.inr ⟨_, _, _, hcol⟩

/-- **Full `U1` Turn-Head Collision Extraction (`u1TurnHead_eq_or_collision`):**
Two `U1` boundary chains hashing to one `turnChainRoot` agree on `weightRoot`, `promptLen`,
`promptRoot`, every intermediate layer boundary `boundaryRoots[0 .. L]`, `u1ProofDigest`, `rawLen`,
and `rawRoot` — OR constructively exhibit a `FramedXofCollision cshakeC`! -/
theorem u1TurnHead_eq_or_collision
    (w₁ p₁ : Digest256) (pl₁ : Nat) (bs₁ : List Digest256) (pf₁ : Digest256) (rl₁ : Nat) (rr₁ : Digest256)
    (w₂ p₂ : Digest256) (pl₂ : Nat) (bs₂ : List Digest256) (pf₂ : Digest256) (rl₂ : Nat) (rr₂ : Digest256)
    (hhead : u1TurnHead w₁ p₁ pl₁ bs₁ pf₁ rl₁ rr₁ = u1TurnHead w₂ p₂ pl₂ bs₂ pf₂ rl₂ rr₂) :
    (w₁ = w₂ ∧ pl₁ = pl₂ ∧ p₁ = p₂ ∧ bs₁ = bs₂ ∧ pf₁ = pf₂ ∧ rl₁ = rl₂ ∧ rr₁ = rr₂) ∨
    ∃ cust left right, FramedXofCollision cshakeC cust left right := by
  unfold u1TurnHead at hhead
  rcases cshake256D256_eq_or_collision _ _ _ hhead with hfr | hcol
  · have hinj := streamCodec_encode_injective u1OutFrameCodec hfr
    simp only [Prod.mk.injEq] at hinj
    rcases hinj with ⟨hchain, hlen, hpf, hrl, hrr⟩
    rcases u1ChainFold_eq_or_collision w₁ p₁ pl₁ bs₁ w₂ p₂ pl₂ bs₂ hlen hchain with
      ⟨hw, hpl, hp, hbs⟩ | hcolChain
    · exact Or.inl ⟨hw, hpl, hp, hbs, hpf, hrl, hrr⟩
    · exact Or.inr hcolChain
  · exact Or.inr ⟨_, _, _, hcol⟩

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

/-- **Capstone Theorem (`verifyAgentTurnBytes_sound_or_collision`):**
Whenever `verifyAgentTurnBytes stmtBytes receiptBytes = true`:
1. `stmtBytes` and `receiptBytes` decode uniquely to canonical `(stmt, rcpt)` (`encodeTurnStmt stmt = stmtBytes`,
   `encodeTurnReceipt rcpt = receiptBytes`), AND
2. For **every** named `(namedPrompt, namedBoundaries, namedProofDigest, namedRaw, namedClean)`
   matching `stmt`'s public commitments (`CommitsAgentTurnChain`), EITHER:
   - **(a) `U1` Model-Production & Layer-Boundary Weld (`Produced` `P8`):**
     `namedPrompt = rcpt.promptBytes`, `namedBoundaries = rcpt.boundaryRoots`,
     `namedProofDigest = rcpt.u1ProofDigest`, `namedRaw = rcpt.wRaw`, `namedClean = rcpt.wClean`,
     `0 < stmt.numLayers`, `namedBoundaries.length = stmt.numLayers + 1`, VRF-selected
     `rcpt.auditedLayer < stmt.numLayers` equals `u1VrfSelectLayer ...`, and `namedBoundaries`
     matches `(rcpt.auditedBInRoot, rcpt.auditedBOutRoot)` at `(auditedLayer, auditedLayer + 1)`;
   - **(b) Canonical Secret Sanitization & Universal Padded-Complement Absence:**
     `namedClean = redactBytes defaultSecretRules namedRaw`, `RedactsTo defaultSecretRules namedRaw namedClean`,
     every `rt ∈ defaultSecretRules` satisfies `AbsentPlain namedClean rt.pat` AND
     `MatchesRegex namedClean (Regex.paddedComplement (Regex.literal rt.pat))`, and clean raw
     inputs suffer zero mangling (`(∀ r ∈ defaultSecretRules, AbsentPlain namedRaw r.pat) → namedClean = namedRaw`);
   - **(c) Unique LL(1) `MiniValue` AST Extraction:**
     `∃ rs, resolveRuleIndices miniJsonCfg.rules rcpt.ruleIndices = some rs ∧ AttrReplay miniJsonCfg rs namedClean stmt.claimedAst ∧ namedClean ∈ miniJsonCfg.toCfg.language`,
     AND for EVERY `rs'` and `ast'`, `AttrReplay miniJsonCfg rs' namedClean ast' → ast' = stmt.claimedAst` —
   **OR** an explicit `cSHAKE256` `FramedXofCollision cshakeC` exists! -/
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
          namedBoundaries[rcpt.auditedLayer + 1]? = some rcpt.auditedBOutRoot ∧
          u1TurnHead stmt.weightRoot stmt.promptRoot stmt.promptLength
            namedBoundaries namedProofDigest stmt.rawLength stmt.rawRoot = stmt.turnChainRoot) ∧
         (namedClean = redactBytes defaultSecretRules namedRaw ∧
          RedactsTo defaultSecretRules namedRaw namedClean ∧
          (∀ rt ∈ defaultSecretRules,
            AbsentPlain namedClean rt.pat ∧
            MatchesRegex namedClean (Regex.paddedComplement (Regex.literal rt.pat)) ∧
            Regex.derives namedClean (Regex.paddedComplement (Regex.literal rt.pat)) = true) ∧
          ((∀ r ∈ defaultSecretRules, AbsentPlain namedRaw r.pat) → namedClean = namedRaw)) ∧
         ((∃ rs, resolveRuleIndices miniJsonCfg.rules rcpt.ruleIndices = some rs ∧
            AttrReplay miniJsonCfg rs namedClean stmt.claimedAst ∧
            namedClean ∈ miniJsonCfg.toCfg.language) ∧
          (∀ (rs' : List (AttrRule UInt8 MiniNT MiniOp)) (ast' : MiniValue),
            AttrReplay miniJsonCfg rs' namedClean ast' → ast' = stmt.claimedAst))) ∨
        ∃ cust left right, FramedXofCollision cshakeC cust left right := by
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
                      refine ⟨⟨rfl, rfl, rfl, rfl, rfl, hLpos, hbLen, haLt, haVrf, hbIn, hbOut, hturnHead⟩,
                        ⟨hred, hred ▸ redactsTo_redactBytes defaultSecretRules rcpt.wRaw, ?_,
                          fun hcl => hred.trans (redactBytes_preserves_clean_plain defaultSecretRules rcpt.wRaw hcl)⟩,
                        ⟨⟨rs, rfl, hrep, attrReplay_mem_language hrep⟩,
                          fun rs' ast' hrep' => (attrReplay_unique_of_ll1 miniJsonCfg hll1 hrep' hrep).1⟩⟩
                      intro rt hrt
                      have hsc := redactBytes_scrubs_padded_complement defaultSecretRules hsafe rt hrt rcpt.wRaw
                      rwa [← hred] at hsc
                    · exact Or.inr ⟨_, _, _, hcCol⟩
                  · exact Or.inr ⟨_, _, _, hrCol⟩
                · exact Or.inr hu1Col
              · exact Or.inr ⟨_, _, _, hpCol⟩

/-! ## §5. Query-Indexed `CertificateComposition` (`P8` `Produced` + `P5` `cert_and`) Weld -/

/--Sanitized secret-absence predicate on raw model output `wRaw`. -/
def SanitizedSecretAbsent (wRaw : List UInt8) : Prop :=
  ∀ rt ∈ defaultSecretRules,
    AbsentPlain (redactBytes defaultSecretRules wRaw) rt.pat ∧
    MatchesRegex (redactBytes defaultSecretRules wRaw) (Regex.paddedComplement (Regex.literal rt.pat))

/-- Unique LL(1) `miniJsonCfg` AST predicate on sanitized `redactBytes defaultSecretRules wRaw`. -/
def ExtractsUniqueAst (claimedAst : MiniValue) (wRaw : List UInt8) : Prop :=
  (∃ rs, AttrReplay miniJsonCfg rs (redactBytes defaultSecretRules wRaw) claimedAst) ∧
  (∀ rs' ast', AttrReplay miniJsonCfg rs' (redactBytes defaultSecretRules wRaw) ast' → ast' = claimedAst)

/-- **`P8` + `P5` Query-Indexed Straightline Composition (`verifiableAgentTurn_produced_and_cert_weld`):**
Instantiates `Assurance.CertificateComposition.cert_and` (`P5`) to conjoin secret-absence (`V_san`)
and unique LL(1) AST extraction (`V_ast`) over `S_raw`, and welds them to `U1` model-production
(`ProducedSound E S_raw IsQwenTurnOutput V_u1 ε_u1`) via `cert_produced_weld` (`P8`) +
`bridgeSound_same_scheme` at total soundness error
`ε_u1 q + (ε_san q + ε_ast q + S_raw.bindAdv q) + S_raw.bindAdv q`. -/
theorem verifiableAgentTurn_produced_and_cert_weld
    {Model PromptDigest DigestRaw OpRaw U1Proof SanProof AstProof : Type}
    [DecidableEq DigestRaw]
    {E : QueryEnv UInt8}
    (S_raw : ContentScheme UInt8 DigestRaw OpRaw)
    {IsQwenTurnOutput : Model → PromptDigest → List UInt8 → Prop}
    {V_u1 : Model → PromptDigest → DigestRaw → U1Proof → Bool}
    {V_san : DigestRaw → SanProof → Bool}
    {V_ast : DigestRaw → AstProof → Bool}
    (claimedAst : MiniValue)
    {ε_u1 ε_san ε_ast : Nat → ℝ}
    (hu1 : ProducedSound E S_raw IsQwenTurnOutput V_u1 ε_u1)
    (hsan : CertSound E S_raw V_san SanitizedSecretAbsent ε_san)
    (hast : CertSound E S_raw V_ast (ExtractsUniqueAst claimedAst) ε_ast)
    (hbind : BindSound E S_raw) :
    ∃ ext_out : Model → PromptDigest → DigestRaw → U1Proof → E.Log → List UInt8,
      ∀ (q : Nat) (m : E.Coins q → Model) (cin : E.Coins q → PromptDigest)
        (cout cout' : E.Coins q → DigestRaw)
        (πu1 : E.Coins q → U1Proof) (πc : E.Coins q → SanProof × AstProof)
        (_πb : E.Coins q → Unit) (log : E.Coins q → E.Log),
        E.ValidLog q log →
        BindingGame.prob (fun ω =>
          (V_u1 (m ω) (cin ω) (cout ω) (πu1 ω) &&
           (V_san (cout' ω) (πc ω).1 && V_ast (cout' ω) (πc ω).2) &&
           decide (cout ω = cout' ω)) = true ∧
          ¬ (E.Grounded (log ω) (ext_out (m ω) (cin ω) (cout ω) (πu1 ω) (log ω)) ∧
              IsQwenTurnOutput (m ω) (cin ω) (ext_out (m ω) (cin ω) (cout ω) (πu1 ω) (log ω)) ∧
              (SanitizedSecretAbsent (ext_out (m ω) (cin ω) (cout ω) (πu1 ω) (log ω)) ∧
               ExtractsUniqueAst claimedAst (ext_out (m ω) (cin ω) (cout ω) (πu1 ω) (log ω)))))
          ≤ ε_u1 q + (ε_san q + ε_ast q + S_raw.bindAdv q) + S_raw.bindAdv q :=
  cert_produced_weld hu1 (cert_and S_raw hsan hast hbind) (bridgeSound_same_scheme S_raw hbind)

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
  have _haLt2 : u1VrfSelectLayer weightRoot boundaryRoots
      (contentCommit256 (redactBytes defaultSecretRules wRaw)) numLayers + 1 < boundaryRoots.length := by
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

/-- **Falsifier 1 (`TK` Prompt Splice Refused or Collision):**
Any accepted receipt whose `promptBytes` differs from the honest `namedPrompt` committed at
`(stmt.promptLength, stmt.promptRoot)` either fails length immediately (`verifyAgentTurnBytes = false`)
or constructively exhibits a `cSHAKE256` `FramedXofCollision`. -/
theorem tk_prompt_mismatch_falsifier
    (stmt : VerifiableAgentTurnStmt) (rcpt : VerifiableAgentTurnReceipt)
    (namedPrompt : List UInt8)
    (hnpLen : namedPrompt.length = stmt.promptLength)
    (hnpRoot : contentCommit namedPrompt = ofDigest256 stmt.promptRoot)
    (hdiff : rcpt.promptBytes ≠ namedPrompt) :
    verifyAgentTurnBytes (encodeTurnStmt stmt) (encodeTurnReceipt rcpt) = false ∨
    ∃ cust left right, FramedXofCollision cshakeC cust left right := by
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
          · exact ⟨_, _, _, hcol⟩

/-- **Falsifier 2 (`TK` Intermediate Boundary Splice Refused or Collision):**
Splicing ANY intermediate layer boundary (`rcpt.boundaryRoots ≠ namedBoundaries`, e.g. mutating
`boundaryRoots[3]`) against a fixed `stmt` either causes `verifyAgentTurnBytes` to reject (`= false`)
or constructively yields a `cSHAKE256` `FramedXofCollision` from `u1TurnHead`. -/
theorem tk_boundary_mismatch_falsifier
    (stmt : VerifiableAgentTurnStmt) (rcpt : VerifiableAgentTurnReceipt)
    (namedBoundaries : List Digest256) (namedProofDigest : Digest256)
    (hnturn : u1TurnHead stmt.weightRoot stmt.promptRoot stmt.promptLength
      namedBoundaries namedProofDigest stmt.rawLength stmt.rawRoot = stmt.turnChainRoot)
    (hdiff : rcpt.boundaryRoots ≠ namedBoundaries) :
    verifyAgentTurnBytes (encodeTurnStmt stmt) (encodeTurnReceipt rcpt) = false ∨
    ∃ cust left right, FramedXofCollision cshakeC cust left right := by
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

set_option maxRecDepth 30000 in
/-- **Falsifier 3 (Unredacted `sk-proj-...` CoT Rejected Unconditionally):**
Supplying unredacted `sampleQwenTurnRaw` as `rcpt.wClean` fails `verifyAgentTurnBytes` unconditionally
for **every** `stmt` and **every** receipt! -/
theorem unredacted_cot_secret_falsifier
    (stmt : VerifiableAgentTurnStmt) (rcpt : VerifiableAgentTurnReceipt)
    (hraw : rcpt.wRaw = sampleQwenTurnRaw) (hclean : rcpt.wClean = sampleQwenTurnRaw) :
    verifyAgentTurnBytes (encodeTurnStmt stmt) (encodeTurnReceipt rcpt) = false := by
  have hne : sampleQwenTurnRaw ≠ redactBytes defaultSecretRules sampleQwenTurnRaw := by decide
  unfold verifyAgentTurnBytes
  rw [decodeTurnStmt_encodeTurnStmt, decodeTurnReceipt_encodeTurnReceipt]
  dsimp only
  unfold verifyAgentTurn verifyAgentTurnWithCfg
  rw [hraw, hclean]
  simp [hne]

/-- **Falsifier 4 (Duplicate-Key JSON Splice & Ambiguous Grammar Refused):**
1. `verifyAgentTurnWithCfg` unconditionally rejects `ambigMiniJsonCfg` (`= false`),
2. `ll1Parse miniJsonCfg ambigSplicePayload = none` (duplicate-key splice payload refused), AND
3. Unlike `ambigMiniJsonCfg` (which yields `ambigBenignAst ≠ ambigDestructiveAst` on `ambigSplicePayload`),
   `miniJsonCfg` forbids any two distinct ASTs on any transcript `w`. -/
theorem duplicate_key_splice_refused
    (stmt : VerifiableAgentTurnStmt) (rcpt : VerifiableAgentTurnReceipt) :
    verifyAgentTurnWithCfg ambigMiniJsonCfg stmt rcpt = false ∧
    ll1Parse miniJsonCfg ambigSplicePayload = none ∧
    (∀ (w : List UInt8) (rs₁ rs₂ : List (AttrRule UInt8 MiniNT MiniOp)) (ast₁ ast₂ : MiniValue),
      AttrReplay miniJsonCfg rs₁ w ast₁ → AttrReplay miniJsonCfg rs₂ w ast₂ → ast₁ = ast₂) := by
  have hambig : ll1Deterministic ambigMiniJsonCfg = false := ambigMiniJsonCfg_splice_attack.1
  refine ⟨?_, ambigMiniJsonCfg_splice_attack.2.2.2.2.2, fun w rs₁ rs₂ ast₁ ast₂ h₁ h₂ =>
    (attrReplay_unique_of_ll1 miniJsonCfg miniJsonCfg_is_ll1 h₁ h₂).1⟩
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
  "564153544d543031d1515a4686f04277fe1eeb478ad7354cc6293437ad521e74bf5cb4c27d3e0c6d96ff8beab9071d6766c0e64795a41a280f7f6d1935abd8f0fbaba44a3b1fd5ac8d5018ffb8a13e59b477c79c7107623299e507da911b92a3f015a80d6f58e3aaa5aa244c5bff5ec49615e87f2f585d607e9e09289d87bc3c72d21fcf18e432a4ac7add9df2315fff44ebafea4337c7f55169e3dd79d546e713b733c990b0a19c71d7d2f5941e05a80522ff4b6579205b52454441435445445f4150495f4b45595d206f6e2064625f737461676509ff61756469745f63666708ff64625f737461676540ff"

/-- Exact `1,415`-byte `VAGENT01` receipt emitted by the live 24-layer integer `Qwen3.5-0.8B` agent CLI. -/
def liveQwen35ReceiptHex : String :=
  "564147454e54303196ff20414d543d31300a7b22636f74223a224b657920736b2d70726f6a2d64656d6f3031206f6e2064625f7374616765222c22746f6f6c223a2261756469745f636667222c22746172676574223a2264625f7374616765222c22616d6f756e74223a31307d0a4b45593d736b2d70726f6a2d396638613762366335643465205441524745543d7661756c745f70726f6420414d543d36340a19fffde6cfaa7947052de6c22cf1ecd0601d5d45e75be48389686d2a9f08d55303f571d33f6ab9b656c0b9888b9ad5623d9165e83000521e67c036eb96b85adcdb8f0cd3688bce8c2bbfe5351c654e05dbfab8389ce981421801b45e7a4049eb132cd9e80d6d4024b2cf98fc6e4eae3910047858626a6132a304a35137827cff745cc51cdc17e71a3da8b996f236d50ceed8d656bb9c8a6fd3c272732cb6795b625885d622128c2eb892997f4bec51888eb9881668565dbe467d62b46a534cf5722072e56d2ef17e02fe095fb932cc8147a9d0b55cb77f2f6f9802dd9595dbba187fa9adc7f45393eebd202a3242897bd66fe17b2ebcd89bdbe04406ffed0830c77062a9da8275a501eb02e47526239cf53f6217e87fdfbf27e31222663b64401b14d324c03e8485e2c3c1da3ffa6672ffac2776a68c90cb211691e45e98e94c62bbe028adb08460416da08ee8e366eafdc40be1feae3026ae88833db9cbe327daa1c6217a0570334eec77f4b8c280a73fd0110766f6eeb05efb4deb7d157efe6bca408fd87d9bff4759545afe85021861c7536aeb80d0bde1a591b39316ca321a4886ca37ec6a2bcd9c83df0530826ff20cc4f611103fa1878eea9940d61d044114b7efd9ee2681b9b20b2707ccf4fcfd0fded3c12b4e34d3d11f522211b3630c8a411f563e919e5e673972f2709088ffa66b5280b5aca45bbc92568c1e5552dc496190bd106d1abc8aef03fa07dff530d46e2503124199c9d3caa8774fedd8c65036cc76d667e36efbb9321c245e5e88f47daf96d0d67212aa45635d544c45529f83d7c5cbc9201fdf8320d846e80d92b9e4ec6a9ff1744bc067f417fd762ebb93432b4ddb3300b377c6fa599afcf24e22cb67e362b31f6941e71dc6fdae5c93e74f66e92e382d8344b7ab3a4974f7d90da5c5779bbdd1fbf6f2c017126dde3f4d06466c2cb03bfb737c7e0e066c6ed22c4c17bd69df6a1afb74373ac5860a6a62ebbe33f96cf948d5105a2bea14bf2b1ecfab5d516bac6051d89eb897f94c2e0563855ac19b707f8b79a61bd990705e83453d52cd14a18f45609bde53918c7612c2f77ba96cf6c707fee8808f4d8030741c3ccfc028cd078ddc2e642103e0923d0cff408fd87d9bff4759545afe85021861c7536aeb80d0bde1a591b39316ca321a4886ca37ec6a2bcd9c83df0530826ff20cc4f611103fa1878eea9940d61d04411464d484a50735730a892cfa618eb936aa4cc945492f63003bcee016d803310cae5bff7b22636f74223a224b657920736b2d70726f6a2d64656d6f3031206f6e2064625f7374616765222c22746f6f6c223a2261756469745f636667222c22746172676574223a2264625f7374616765222c22616d6f756e74223a36347d5fff7b22636f74223a224b6579205b52454441435445445f4150495f4b45595d206f6e2064625f7374616765222c22746f6f6c223a2261756469745f636667222c22746172676574223a2264625f7374616765222c22616d6f756e74223a36347d52ffff0fff01ff0fff04ff06ff0fff0fff10ff58ff71ff85ff2eff68ff5fff52ff51ff4eff50ff61ff52ff51ff6bff4eff5dff56ff6bff58ff52ff66ff69ff2eff7bff7aff2eff70ff6eff6bff7fff80ff6dff73ff71ff12ff0fff0fff0fff0fff10ff6dff81ff70ff75ff80ff6bff6fff72ff73ff12ff0fff0fff0fff0fff10ff70ff6eff6bff7fff80ff6dff73ff71ff12ff0fff0fff0fff0fff20ff28ff1aff0fff0fff"

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
      rcpt.auditedLayer == 12 &&
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
/-- info: 'Minidregg.Assurance.VerifiableAgentTurnWeld.verifiableAgentTurn_produced_and_cert_weld' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms verifiableAgentTurn_produced_and_cert_weld
/-- info: 'Minidregg.Assurance.VerifiableAgentTurnWeld.verifyAgentTurnBytes_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms verifyAgentTurnBytes_complete
/-- info: 'Minidregg.Assurance.VerifiableAgentTurnWeld.verifyAgentTurnBytes_premises_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms verifyAgentTurnBytes_premises_inhabited
/-- info: 'Minidregg.Assurance.VerifiableAgentTurnWeld.tk_prompt_mismatch_falsifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tk_prompt_mismatch_falsifier
/-- info: 'Minidregg.Assurance.VerifiableAgentTurnWeld.tk_boundary_mismatch_falsifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tk_boundary_mismatch_falsifier
/-- info: 'Minidregg.Assurance.VerifiableAgentTurnWeld.unredacted_cot_secret_falsifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms unredacted_cot_secret_falsifier
/-- info: 'Minidregg.Assurance.VerifiableAgentTurnWeld.duplicate_key_splice_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms duplicate_key_splice_refused

end Minidregg.Assurance.VerifiableAgentTurnWeld
