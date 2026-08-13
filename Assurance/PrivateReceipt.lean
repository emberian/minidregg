/-
# `Assurance/PrivateReceipt.lean` — can a turn carry a PRIVATE input? (the checkpoint)

The honest answer to "do we actually have hiding / private inputs" was: we have the algebraic
HIDING CORE (`Selvage/ZKHiding.lean` — masked-opening hiding for Reed–Solomon), but no wired
"a turn carries a hidden witness" feature and no end-to-end ZK argument. This file takes the
FIRST real step, statement-first: it makes "private input to a turn" a concrete object with a
kill-checkpoint, and answers — at the opening layer — YES, the architecture admits it.

**The model.** A turn's receipt (`Assurance/ReceiptClaim.lean`) is committed as a codeword and
the verifier learns it only through `t` spot-check openings (WHIR/BCS). "The turn has a private
input" means: some of what the receipt encodes is a PRIVATE witness the verifier must NOT learn,
while still being convinced the turn is valid. The private witness IS the committed word; the
leakage surface is exactly the `t` opened symbols.

**The checkpoint.** `privateReceipt_hiding`: masking the receipt codeword (add a uniform mask
codeword, `mask f γ r = f + γ • r`) makes those `t` openings *perfectly simulatable* — reused
from `rs_maskedOpeningHiding`. `privateReceipt_witness_hidden`: two turns carrying DIFFERENT
private witnesses produce IDENTICAL opened-symbol supports (`MaskedOpeningHiding.witness_free`) —
the verifier watching the spot-check cannot tell which private witness the turn held. That is
the private-input property, machine-checked at this layer.

**Verdict (v0): YES, at the opening layer — the receipt admits a hidden witness.** Both dials are
load-bearing, not vacuous: `witness_hidden_needs_mask` shows that at `γ = 0` (no mask) the
private witness IS leaked (the opened support collapses to the witness's own symbols), and the
`t ≤ d` bound is load-bearing upstream (`not_maskedOpeningHiding_of_gt`). What this does NOT yet
give — stated plainly — is `[OB-4-hiding-rbr]` (the full zero-knowledge argument where hiding and
SOUNDNESS coexist in one straightline RBR game, against a real prover): that is Selvage's open
contribution slot, confirmed absent from the literature, and most of OB-4's mass. So: the
private-input story is *possible* (this checkpoint), not *finished* (that residual).
-/
import Assurance.ReceiptClaim
import Selvage.ZKHiding

namespace Minidregg.Assurance

open Minidregg.Kernel Minidregg.Selvage

variable {F : Type} [Field F]

/-- **The private-input hiding of a receipt codeword.** When a turn's receipt is committed as a
Reed–Solomon codeword and masked by a uniform mask codeword, the `t ≤ d` spot-check openings the
verifier reads are perfectly simulatable — the private witness in the codeword does not leak
through the openings. This is the masked-opening hiding of `Selvage/ZKHiding.lean` at the receipt's
own code; it is the substrate on which "a turn carries a private input" rests. -/
theorem privateReceipt_hiding {ι : Type} [Fintype ι] {t d : ℕ}
    (dom : ι ↪ F) (ht : t ≤ d) {q : Fin t → ι}
    (hq : Function.Injective (dom ∘ q)) {γ : F} (hγ : γ ≠ 0) :
    MaskedOpeningHiding (reedSolomonCode dom d) q γ :=
  rs_maskedOpeningHiding dom ht hq hγ

/-- **The private witness is hidden — the checkpoint.** Two turns carrying DIFFERENT private
witnesses (`f₁ ≠ f₂`, the two committed receipt words) produce the SAME opened-symbol support
under masking: the verifier's `t`-symbol spot-check cannot distinguish which private witness the
turn held. A turn *can* carry a hidden input. Rides `MaskedOpeningHiding.witness_free`; the
distributions coincide exactly (perfect, not computational — a simulator samples the `t` symbols
uniformly and never sees the witness). -/
theorem privateReceipt_witness_hidden {ι : Type} [Fintype ι] {t d : ℕ}
    (dom : ι ↪ F) (ht : t ≤ d) {q : Fin t → ι}
    (hq : Function.Injective (dom ∘ q)) {γ : F} (hγ : γ ≠ 0)
    (f₁ f₂ : ι → F) :
    (fun r => openSymbols q (mask f₁ γ r)) '' (reedSolomonCode dom d)
      = (fun r => openSymbols q (mask f₂ γ r)) '' (reedSolomonCode dom d) :=
  (privateReceipt_hiding dom ht hq hγ).witness_free f₁ f₂

/-! ### The mask is load-bearing — without it, the private input LEAKS.

The teeth: at `γ = 0` the masked word is just `f`, so the opened support is exactly `f`'s own
`t` symbols — a fixed set that DOES depend on the witness. Hiding fails; the private input is
revealed. So the mask is not decoration: it is what makes the input private. -/

/-- **[teeth] The private-input hiding genuinely needs the mask.** `MaskedOpeningHiding` is FALSE
at `γ = 0`: the opened support collapses to the witness's own symbols (`not_maskedOpeningHiding_zero`).
Without masking, the verifier's spot-check reads the private witness directly. -/
theorem witness_hidden_needs_mask {ι : Type} [Fintype ι] {t d : ℕ}
    (dom : ι ↪ F) {q : Fin t → ι} (htpos : 0 < t) :
    ¬ MaskedOpeningHiding (reedSolomonCode dom d) q (0 : F) :=
  not_maskedOpeningHiding_zero (reedSolomonCode dom d) htpos

/-! ### Keystone witnesses — the checkpoint FIRES concretely (ZMod 5, the rate-1/2 code).

Reusing `Selvage/ZKHiding.lean`'s built RS example (`dom₅ : Fin 4 ↪ ZMod 5`, degree bound 2, the
two-symbol query `qPair = ![0,2]`). Two turns whose private witnesses are two DISTINCT lines
(`3 + 0·X` vs a different codeword) are indistinguishable under masking; at `γ = 0` they are not.
-/

/-- *Satisfiable + premise-inhabitation*: the private-input hiding fires for the receipt code at a
real nonzero challenge — a turn CAN hide its witness. -/
theorem privateReceipt_hiding_fires {γ : ZMod 5} (hγ : γ ≠ 0) :
    MaskedOpeningHiding (reedSolomonCode RSExample.dom₅ 2) ZkHidingExample.qPair γ :=
  privateReceipt_hiding RSExample.dom₅ (by decide) ZkHidingExample.qPair_inj hγ

/-- *The checkpoint fires*: two DISTINCT private witnesses (two codewords) give identical opened
supports at `γ = 1` — the verifier cannot tell them apart. -/
theorem privateReceipt_witness_hidden_fires (f₁ f₂ : Fin 4 → ZMod 5) :
    (fun r => openSymbols ZkHidingExample.qPair (mask f₁ (1 : ZMod 5) r)) '' (reedSolomonCode RSExample.dom₅ 2)
      = (fun r => openSymbols ZkHidingExample.qPair (mask f₂ (1 : ZMod 5) r)) '' (reedSolomonCode RSExample.dom₅ 2) :=
  privateReceipt_witness_hidden RSExample.dom₅ (by decide) ZkHidingExample.qPair_inj (by decide) f₁ f₂

/-- *Teeth, concrete*: at `γ = 0` hiding is refuted on the receipt code — the private input leaks. -/
theorem privateReceipt_leaks_at_zero :
    ¬ MaskedOpeningHiding (reedSolomonCode RSExample.dom₅ 2) ZkHidingExample.qPair (0 : ZMod 5) :=
  witness_hidden_needs_mask RSExample.dom₅ (by decide)

/-! ### Honest residual — what "possible" is NOT

`[PRIVATE-INPUT-rbr]` (= `[OB-4-hiding-rbr]`, the shared contribution slot): this checkpoint
proves the OPENING layer hides the private witness (perfect, at `t ≤ d`, `γ ≠ 0`). The full
private-input guarantee needs three more things, none built here and none stubbed:
  1. the mask confined to the mask-claim's solution space (constrained-mask surjectivity), so
     masking does not disturb the low-degree test — reduced by `maskedOpeningHiding_of_surj` to
     ONE statement, realizer named in `Selvage/ZKHiding.lean`;
  2. hiding and SOUNDNESS coexisting in one straightline RBR game (the extractor peels the mask
     via `unmask` while the simulator hides it) — the genuinely open research half;
  3. the wire-up to a `KernelState`'s designated PRIVATE fields (which coordinates of `flatten`
     are witness vs public) as a first-class turn feature — a kernel/model design step, not yet
     taken (the kernel is still the 5-file spine; a private-witness turn type does not exist).
So: private inputs are POSSIBLE in this architecture — the receipt admits a hidden witness whose
spot-checks are simulatable — but they are not yet a finished, sound, wired feature.
-/

end Minidregg.Assurance
