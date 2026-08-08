/-
# `Assurance/PrivateTurn.lean` — the private-witness TURN (the model, Lean-authored)

`Assurance/PrivateReceipt.lean` proved the OPENING layer hides a witness. This file names the
first-class object ember asked for: a **private-witness turn** — a turn that reveals a PUBLIC
statement (its declared effect) while carrying a PRIVATE witness the verifier never learns.

**Substrate, said out loud (the tripwire, CLAUDE.md):** this is a Lean-authored MODEL and its
constraints are Lean-authored. breadstuffs `circuit-prove/faithful_note_spend_exact_v3` (hidden
note-opening + exact-nullifier + depth-16 membership) is the DESIGN reference for the shape —
nothing more. Its Rust AIRs (`*_air.rs`, `dregg_circuit` descriptors) are DEBT; they are NOT
imported, ported, or extended. The turn's constraint system is `[PRIVATE-TURN-air]` below —
Lean-authored, not yet built — and this file is honest that it does not exist yet.

**The model.** A private-witness turn splits into:
  * a PUBLIC statement — the accumulator CLAIM (`AccClaim`): the turn's declared effect (value
    conservation, the revealed nullifier), checked by the decider without the witness;
  * a PRIVATE witness — the receipt WORD (`flatten` of the post-state, note values and all),
    committed and revealed to the verifier only through masked `t`-symbol openings.
The two-part guarantee: the public claim BINDS (the decider checks it — `Loom/Decider.lean`),
and the private witness HIDES (two turns with the same public claim but different witnesses are
indistinguishable — `Loom/ZKHiding.lean`'s `witness_free`, via `PrivateReceipt`).

**Verdict (v0): the private-witness turn is a real object, and its hiding half is proved.**
`privateTurn_witness_hidden`: two private turns sharing a public claim, carrying DIFFERENT
private witnesses, produce IDENTICAL masked openings — the verifier cannot tell which witness
the turn held. What is NOT built, stated plainly: `[PRIVATE-TURN-air]` (the Lean-authored
note-opening / nullifier-derivation / membership constraint system — the real content, and it
must NOT be the ported Rust AIR), and `[ZK-RBR-game]` (soundness coexisting with hiding — the
open research half, `Loom/ZkArgument.lean`). So: the private-witness turn EXISTS and HIDES; it
does not yet SOUNDLY CONSTRAIN. That gap is Lean-authored work, named, not faked.
-/
import Assurance.PrivateReceipt

namespace Minidregg.Assurance

open Minidregg.Kernel Minidregg.Loom

variable {F : Type} [Field F]

/-- A **private-witness turn** over a Reed–Solomon receipt code: the private witness is the
committed word `w` (the note details), and the turn's PUBLIC statement is carried by the code +
the masking challenge. The receipt is `w` committed as an RS codeword; the verifier reads it
only through masked `t`-symbol openings. `q` are the spot-check positions, `γ ≠ 0` the mask
challenge. -/
structure PrivateTurn (ι : Type) [Fintype ι] (F : Type) [Field F] (t d : ℕ) where
  /-- the evaluation domain of the receipt code. -/
  dom : ι ↪ F
  /-- degree bound: `t ≤ d` (the opening budget is within the code). -/
  ht : t ≤ d
  /-- the verifier's `t` spot-check positions. -/
  q : Fin t → ι
  /-- the spot-checks are at distinct domain points. -/
  hq : Function.Injective (dom ∘ q)
  /-- the mask challenge (nonzero — the mask is what makes the witness private). -/
  γ : F
  hγ : γ ≠ 0

/-- **The private witness hides — the turn model's hiding half.** Two private-witness turns with
the SAME public parameters but carrying DIFFERENT private witnesses `w₁ ≠ w₂` produce IDENTICAL
masked-opening supports: the verifier's `t`-symbol spot-check cannot distinguish which witness
the turn held. This is the private-input property lifted to the turn object; it rides
`PrivateReceipt.privateReceipt_witness_hidden` (perfect, not computational — the simulator
samples the `t` symbols uniformly and never sees the witness). -/
theorem privateTurn_witness_hidden {ι : Type} [Fintype ι] {t d : ℕ}
    (T : PrivateTurn ι F t d) (w₁ w₂ : ι → F) :
    (fun r => openSymbols T.q (mask w₁ T.γ r)) '' (reedSolomonCode T.dom d)
      = (fun r => openSymbols T.q (mask w₂ T.γ r)) '' (reedSolomonCode T.dom d) :=
  privateReceipt_witness_hidden T.dom T.ht T.hq T.hγ w₁ w₂

/-- **The mask is what makes the turn private.** Strip the mask (`γ = 0`) and the turn's witness
LEAKS: masked-opening hiding is false, so the spot-check reads the witness directly. The privacy
is not incidental to the turn — it is exactly the nonzero mask. -/
theorem privateTurn_needs_mask {ι : Type} [Fintype ι] {t d : ℕ}
    (dom : ι ↪ F) {q : Fin t → ι} (htpos : 0 < t) :
    ¬ MaskedOpeningHiding (reedSolomonCode dom d) q (0 : F) :=
  witness_hidden_needs_mask dom htpos

/-! ### Keystone — a concrete private-witness turn that HIDES (ZMod 5, the receipt code).

Reusing the built RS example (`RSExample.dom₅ : Fin 4 ↪ ZMod 5`, `d = 2`, `qPair = ![0,2]`,
`γ = 1`). Two turns whose private witnesses are two DISTINCT words (two different note ledgers)
are indistinguishable to the verifier's spot-check. -/

/-- A concrete private-witness turn over the F₅ receipt code — premise-inhabitation: the object
exists with a real nonzero mask. -/
def turn₅ : PrivateTurn (Fin 4) (ZMod 5) 2 2 :=
  { dom := RSExample.dom₅, ht := by decide, q := ZkHidingExample.qPair,
    hq := ZkHidingExample.qPair_inj, γ := 1, hγ := by decide }

/-- *The checkpoint FIRES*: on `turn₅`, two DISTINCT private witnesses give identical opened
supports — a real private-witness turn hides its witness. -/
theorem turn₅_witness_hidden (w₁ w₂ : Fin 4 → ZMod 5) :
    (fun r => openSymbols ZkHidingExample.qPair (mask w₁ (1 : ZMod 5) r)) '' (reedSolomonCode RSExample.dom₅ 2)
      = (fun r => openSymbols ZkHidingExample.qPair (mask w₂ (1 : ZMod 5) r)) '' (reedSolomonCode RSExample.dom₅ 2) :=
  privateTurn_witness_hidden turn₅ w₁ w₂

/-- *Teeth*: strip `turn₅`'s mask and the witness leaks — hiding is refuted at `γ = 0`. -/
theorem turn₅_leaks_without_mask :
    ¬ MaskedOpeningHiding (reedSolomonCode RSExample.dom₅ 2) ZkHidingExample.qPair (0 : ZMod 5) :=
  privateTurn_needs_mask RSExample.dom₅ (by decide)

/-! ### Honest residuals — what a private-witness turn does NOT yet have

`[PRIVATE-TURN-air]` — the Lean-authored constraint system that makes the turn SOUND: the
note-opening relation (the private witness IS a valid note), the exact-nullifier derivation (the
revealed nullifier is the one this note produces), and depth-`m` membership (the note was
committed). breadstuffs `faithful_note_spend_exact_v3` is the design shape; the constraints are
authored in LEAN (a future `air`/gadget compiled from the DSL), never the ported Rust AIR. This
is the real content and it does not exist yet.

`[ZK-RBR-game]` — soundness coexisting with hiding in one straightline argument (`Loom/
ZkArgument.lean`). Until it lands, the public claim's binding rides `Loom/Decider.lean` at the
word level and the hiding rides this file; they are not yet fused against a forging prover.

`[PRIVATE-TURN-kernel]` — the wire-up to a `Kernel/Turn` variant carrying a private witness (the
`umap` commitment/nullifier planes already model the note sets; a private-witness `Hyperedge`
does not exist). A model design step, not taken.

So the private-witness turn is a real object that provably HIDES; making it SOUNDLY CONSTRAIN and
wiring it into the kernel turn are the named, Lean-authored next pieces.
-/

end Minidregg.Assurance
