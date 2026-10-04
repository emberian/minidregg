/-
# `Compiler.GenericSimplexTransferability` — the ML-DSA COMMIT certificate sits at the public pole

`Theory.Transferability` separates transferable (public, non-repudiable) evidence from
designated-verifier (deniable) evidence and proves that a verifier-blind check has an empty
designated pole. This module classifies Mini's agreement evidence object, the Generic Simplex
COMMIT certificate (`GenericSimplexCodec.Certificate`, checked by
`GenericSimplexIO.verifyCertificate` before a `VerifiedCommit` can exist).

* `verifyCertificate_pure` — for any deterministic signature verifier (ML-DSA-65 verify is one),
  the ACTUAL IO check `verifyCertificate` is `pure` of a Boolean function of public data only:
  the pinned `Context` (configuration, epoch, public keys) and the certificate.
* `verdict_ignores_verifier_secret` — the only private capability a node's `Crypto` record carries
  is `sign`; the verdict is the same IO action whatever signing capability the checking node holds.
* `commitIndexed_blind`, `commit_certificate_public_pole`, `commit_certificate_no_designated` —
  hence every accepted COMMIT certificate convinces every holder of the public context, and no
  COMMIT certificate is designated-verifier evidence: it is non-repudiable for its signers
  (given ML-DSA unforgeability, which is a cryptographic premise, not a theorem here).
* `private_return_needs_other_check` — a DV-mode receipt for a private return cannot reuse this
  check: any DV kernel whose verdict is the COMMIT verdict fails `DVReceiptMode`. What it needs
  instead is stated by `Theory.Transferability.DVReceiptMode`: a verifier-secret-dependent check
  with a simulator whose transcripts leave an outsider unconvinced.
* `accepted_certificate_exists` — the acceptance premise is inhabited (a well-formed 4-party
  context, a 3-signer quorum, with a stand-in verify that accepts every signature: the premise
  inhabitant, not a claim about ML-DSA).
-/
import Compiler.GenericSimplexIO
import Theory.Transferability

namespace Minidregg.Compiler.GenericSimplexTransferability

open Minidregg.Kernel.GenericSimplex
open Minidregg.Compiler.GenericSimplexCodec
open Minidregg.Compiler.GenericSimplexIO
open Minidregg.Theory.Transferability

set_option autoImplicit false

/-- A deterministic signature verifier `(publicKey, message, signature) ↦ Bool`. -/
abbrev SigVerify := Bytes → Bytes → Bytes → Bool

/-- A node's `Crypto` record over a deterministic verifier, holding signing capability `sign`. -/
def pureCrypto (verify : SigVerify) (sign : Bytes → IO Bytes) : Crypto :=
  ⟨fun pk message signature => pure (verify pk message signature), sign⟩

/-- One attestation's public check, exactly the loop body of `verifyAttestations`. -/
def attestationOk (verify : SigVerify) (expected : Context) (bytes : Bytes)
    (a : Attestation) : Bool :=
  !(decide (a.signer ≥ expected.config.parties) || a.signature.length != 3309) &&
    match expected.publicKeys[a.signer]? with
    | some pk => verify pk bytes a.signature
    | none => false

/-- The quorum-shape precondition of `verifyAttestations`. -/
def attestationsShape (expected : Context) (signers : List Attestation) : Bool :=
  !(!expected.wellFormed || decide (signers.length < expected.config.quorum) ||
    (signers.map Attestation.signer).eraseDups.length != signers.length)

/-- The verdict of `verifyAttestations` as a function of public data. -/
def attestationsVerdict (verify : SigVerify) (expected : Context) (bytes : Bytes)
    (signers : List Attestation) : Bool :=
  attestationsShape expected signers && signers.all (attestationOk verify expected bytes)

/-- The verdict of `verifyCertificate` as a function of public data. -/
def certificateVerdict (verify : SigVerify) (expected : Context) (cert : Certificate) : Bool :=
  !(cert.context != expected || cert.view == 0 || cert.block.isEmpty) &&
    attestationsVerdict verify expected (commitmentBytes expected cert.view cert.block) cert.signers

/-- `pure`-then-`bind` in `IO` is definitional (Lean 4.30 ships no `LawfulMonad IO` instance). -/
theorem io_pure_bind {α β : Type} (a : α) (f : α → IO β) : (pure a >>= f) = f a := rfl

/-- An early-exit loop whose body, from the running state, yields on `ok` and stops with `false`
otherwise, returns `none` exactly when every element is `ok`. -/
theorem forIn_early_exit {α : Type} (l : List α) (ok : α → Bool)
    (body : α → MProd (Option Bool) PUnit → IO (ForInStep (MProd (Option Bool) PUnit)))
    (hbody : ∀ a, body a ⟨none, PUnit.unit⟩ =
      pure (if ok a then .yield ⟨none, PUnit.unit⟩ else .done ⟨some false, PUnit.unit⟩)) :
    forIn l (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit) body =
      pure ⟨if l.all ok then none else some false, PUnit.unit⟩ := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    rw [List.forIn_cons, hbody a]
    cases h : ok a <;> simp [h, ih, io_pure_bind]

/-- **The actual IO check is a pure function of public data.** -/
theorem verifyAttestations_pure (verify : SigVerify) (sign : Bytes → IO Bytes)
    (expected : Context) (bytes : Bytes) (signers : List Attestation) :
    verifyAttestations (pureCrypto verify sign) expected bytes signers =
      pure (attestationsVerdict verify expected bytes signers) := by
  unfold verifyAttestations attestationsVerdict attestationsShape
  simp only [pureCrypto]
  split
  · rename_i h; simp [h]
  · rename_i h
    rw [forIn_early_exit signers (attestationOk verify expected bytes)]
    · cases hall : signers.all (attestationOk verify expected bytes) <;> simp [h, hall, io_pure_bind]
    · intro a
      unfold attestationOk
      split
      · rename_i hbad; simp [hbad]
      · rename_i hgood
        split
        · rename_i pk hpk; cases hv : verify pk bytes a.signature <;> simp [hgood, hpk, hv, io_pure_bind]
        · rename_i hnone
          have hk : expected.publicKeys[a.signer]? = none := by
            cases h' : expected.publicKeys[a.signer]?
            · rfl
            · exact (hnone _ h').elim
          simp [hgood, hk, io_pure_bind]

/-- **`verifyCertificate` is `pure` of `certificateVerdict`.** -/
theorem verifyCertificate_pure (verify : SigVerify) (sign : Bytes → IO Bytes)
    (expected : Context) (cert : Certificate) :
    verifyCertificate (pureCrypto verify sign) expected cert =
      pure (certificateVerdict verify expected cert) := by
  unfold verifyCertificate certificateVerdict
  split
  · rename_i h; simp [h]
  · rename_i h; rw [verifyAttestations_pure]; simp [h, io_pure_bind]

/-- **The checking node's own secret does not enter the verdict.** Two nodes holding different
signing capabilities run the same IO check on the same public context and certificate. -/
theorem verdict_ignores_verifier_secret (verify : SigVerify) (sign₁ sign₂ : Bytes → IO Bytes)
    (expected : Context) (cert : Certificate) :
    verifyCertificate (pureCrypto verify sign₁) expected cert =
      verifyCertificate (pureCrypto verify sign₂) expected cert := by
  rw [verifyCertificate_pure, verifyCertificate_pure]

/-- The COMMIT check indexed by the checking node's signing capability (its only secret), with
statement = the pinned public context. By `verifyCertificate_pure` this is the verdict of the
actual IO check for each node. -/
@[reducible] def commitIndexed (verify : SigVerify) :
    VerifierIndexed (Bytes → IO Bytes) Context Certificate :=
  ⟨fun _sign expected cert => certificateVerdict verify expected cert⟩

/-- The indexed COMMIT check agrees with the actual IO check for every verifier. -/
theorem commitIndexed_is_verifyCertificate (verify : SigVerify) (sign : Bytes → IO Bytes)
    (expected : Context) (cert : Certificate) :
    verifyCertificate (pureCrypto verify sign) expected cert =
      pure ((commitIndexed verify).verifyFor sign expected cert) :=
  verifyCertificate_pure verify sign expected cert

theorem commitIndexed_blind (verify : SigVerify) :
    @VerifierBlind (Bytes → IO Bytes) Context Certificate (commitIndexed verify) :=
  fun _ _ _ _ => rfl

/-- **The COMMIT certificate is in the public pole.** An accepted certificate convinces every
verifier, whatever secret it holds: transferable and non-repudiable. -/
theorem commit_certificate_public_pole (verify : SigVerify) (sign : Bytes → IO Bytes)
    (expected : Context) (cert : Certificate)
    (accepted : @DischargedFor _ _ _ (commitIndexed verify) sign expected cert) :
    @Transferable (Bytes → IO Bytes) Context Certificate (commitIndexed verify) expected cert :=
  @blind_discharged_transferable _ _ _ (commitIndexed verify) (commitIndexed_blind verify)
    _ _ _ accepted

/-- **No COMMIT certificate is designated-verifier evidence.** -/
theorem commit_certificate_no_designated (verify : SigVerify) (v₀ : Bytes → IO Bytes)
    (expected : Context) (cert : Certificate) :
    ¬ @DesignatedFor _ _ _ (commitIndexed verify) v₀ expected cert :=
  @blind_no_designated _ _ _ (commitIndexed verify) (commitIndexed_blind verify) v₀ expected cert

/-- **A DV-mode receipt for a private return cannot reuse the COMMIT check.** Any designated-verifier
kernel over the same evidence whose verdict IS the COMMIT verdict fails `DVReceiptMode` for every
designated verifier: DV mode needs a check whose verdict depends on the verifier's secret. -/
theorem private_return_needs_other_check {VSecret : Type} (verify : SigVerify)
    (kernel : DVKernel (Bytes → IO Bytes) Context Certificate VSecret)
    (same : ∀ sign expected cert,
      kernel.verifyFor sign expected cert = certificateVerdict verify expected cert)
    (v₀ : Bytes → IO Bytes) :
    ¬ @DVReceiptMode _ _ _ _ kernel v₀ := by
  intro mode
  apply mode.not_blind
  intro v w s p
  show kernel.verifyFor v s p = kernel.verifyFor w s p
  rw [same, same]

/-! ## The acceptance premise is inhabited -/

/-- A well-formed four-party (`f = 1`) context with distinct 1952-byte keys. -/
def sampleContext : Context where
  scope := [1]
  epoch := 0
  instanceBytes := [2]
  config := { parties := 4, faults := 1, timeout := 1 }
  publicKeys := (List.range 4).map fun i => List.replicate 1952 (UInt8.ofNat i)

/-- A three-signer quorum certificate for view 1. -/
def sampleCertificate : Certificate where
  context := sampleContext
  view := 1
  block := [[7]]
  signers := (List.range 3).map fun i => ⟨i, List.replicate 3309 0⟩

/-- With a stand-in verifier that accepts every signature (the premise inhabitant, not a claim
about ML-DSA), the sample certificate is accepted. -/
theorem accepted_certificate_exists :
    certificateVerdict (fun _ _ _ => true) sampleContext sampleCertificate = true := by
  decide +kernel

/-- …and the stand-in verdict is not constant: a sub-quorum certificate is refused. -/
theorem subquorum_certificate_refused :
    certificateVerdict (fun _ _ _ => true) sampleContext
      { sampleCertificate with signers := sampleCertificate.signers.take 2 } = false := by
  decide +kernel

end Minidregg.Compiler.GenericSimplexTransferability
