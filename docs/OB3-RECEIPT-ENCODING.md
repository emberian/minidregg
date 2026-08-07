# OB-3 — the receipt Q as a native accumulated claim (the kill-checkpoint)

*Design, 2026-08-07, under the standing goal. This is the mutual-elaboration crux:
Loom's accumulator shape (from the WARP/WHIR construction reads, LOOM §6) meets the
kernel's receipt Q (HYPEREDGE-DESIGN §4). OB-3 passes iff a turn's receipt claim is
NATIVE to the accumulator — carried in its constraint channel, not proven by a
verifier-simulator circuit. This document states the encoding precisely enough that a
prototype lane can build it and a checkpoint can PASS or FAIL on evidence.*

## 0. The two shapes that must meet

**The receipt Q** (HYPEREDGE-DESIGN §4): a committed turn leaves one Q — the committed
whole post-state of all legs under one commitment scheme, anchored at `apex`. Because
every turn is one hyperedge regardless of arity, Q has ONE shape at every ι. Q must
bind: the post-state of every touched cell, the frame (untouched cells unchanged), the
per-asset balance, the nullifier/evidence growth, and the chain seam.

**The accumulated claim** (LOOM §6, convergent WARP `(rt,α,μ,β,η)` / WHIR multi-
constrained CRS): a word commitment on ONE fixed outermost code + a constraint channel
of (point, target) pairs that are γ-linear in both + a proximity ledger (δ, regime tag,
additive RBR error budget) + OOD uniqueness pins. Closure: CRS-claim × CRS-claim →
CRS-claim under γ-folding; the proximity test defers to one decider descent.

OB-3 succeeds iff Q **is** such a CRS claim — the light-client object is the Q-chain.

## 1. The encoding (what the prototype must build)

1. **Q's committed word.** The post-state projection `uproj` (breadstuffs' UniversalBridge
   design, ported into `Kernel/State.lean`'s keyed map) is a vector over the base field:
   one coordinate per (cell field | keyed-map entry). Encode it under the fixed linear
   code C (RS at v0, `Loom/ReedSolomon.lean`): `f := C(uproj(post))`. **The Merkle root of
   `f` IS Q's commitment `rt`** — Q does not get a *separate* commitment scheme; the
   accumulator's word commitment is Q.
2. **Q's binding = a multilinear-evaluation constraint.** "The receipt binds the whole
   post-state" (the integrity guarantee) becomes `û(α) = μ` at a challenge point α with
   μ the claimed digest — the accumulator's native evaluation claim. Frame-preservation
   (untouched cells unchanged) is the SAME constraint over the untouched coordinates: no
   separate frame circuit, one evaluation over the whole vector.
3. **Per-asset conservation = a linear functional in the constraint channel.** `∑_c bal(c,a)
   = 0` (issuer-well form) is `⟨f, a_conservation⟩ = 0` — a Z-linear constraint `ŵ(Z,X) =
   Z·â(X)` in WHIR's linear-Σ-IOP class (LOOM §6: "the constraint part is algebraically
   linear in the right regime"). It folds by γ-powers with the others.
4. **The chain seam = an accumulated equality.** The turn's `pre-root = prev.post-root`
   (HYPEREDGE-DESIGN §4, LOOM §3 [OB-3′]) is a constraint binding this link's pre-state
   coordinates to the prior accumulator's committed post-root — an encoded-column equality,
   carried in the channel, NOT a side condition. This is the load-bearing claim of the
   whole scheme (it is what makes the aggregate attest a CONTIGUOUS history).
5. **σ before γ** (DeepBrake's message-order rule, LOOM §6): Q's claimed targets (μ, the
   conservation target 0, the seam target) are all fixed at receipt time — before the
   accumulator samples its fold challenge γ. So γ does double duty (evaluation binding
   rides the proximity-tested fold) and no separate binding obligation accrues.

## 2. The checkpoint criterion — what PASS and FAIL look like

**PASS** (v0 milestone): a prototype `Loom/ReceiptClaim.lean` that, given a landed turn's
post-state (`Kernel/Turn.lean` + `Kernel/State.lean`), produces a CRS/`(rt,α,μ,β,η)`-shape
claim and PROVES: (a) the claim's word is `C(uproj post)`; (b) an honest turn's Q satisfies
the claim; (c) the TEETH — a tampered post-state (a mutated untouched cell, a non-conserving
balance, a mis-pointed seam) makes the claim UNSAT (the anti-ghost tooth, now at the
accumulator level not a bespoke circuit); (d) two such claims fold to one CRS claim by the
γ-rule (closure), so the chain is one accumulated object. No verifier-simulator anywhere.

**FAIL** (a real finding, surfaced with evidence, not papered over): if Q needs to bind
something the constraint channel CANNOT carry as a γ-linear (point, target) claim — e.g. a
non-linear relation among post-state coordinates, or a binding that is not an evaluation of
the committed word. Candidate failure sites to probe first:
- **Authority non-amplification** (`granted ≤ held` per delegation edge): is this expressible
  as a linear/low-degree constraint on the encoded caps column, or does it need a lookup
  (WHIR/Arc support lookups — so a lookup leg, not a failure) or something worse?
- **Nullifier non-membership** (freshness): a sorted-tree non-membership opening — is it a
  witnessed-predicate lookup (fine) or does it force a bespoke gadget (a partial fail —
  degrade honestly to "this leg is a lookup argument," don't hide it)?
- **The keyed-map sparsity**: uproj is large and sparse; encoding the WHOLE post-state per
  link may be prohibitive. The honest degrade: encode only the TOUCHED coordinates + a frame
  digest for the rest (BrakeWHIR-style), and prove the frame digest binds the untouched
  remainder. If even that does not fold linearly, that is the finding.

## 3. What each lane feeds

- `Kernel/State.lean` → `uproj`, the post-state vector to encode.
- `Kernel/Turn.lean` → the hyperedge whose commit produces Q; the frame theorem that
  becomes constraint (2).
- `Loom/ReedSolomon.lean` → the code C the word lives in (landed).
- `Loom/Sumcheck.lean` → the reduction that retires the Z-linear part of the accumulated
  constraints at the decider (the front).
- `Loom/Depth.lean` (OB-2/OB-2a) → the straightline soundness the folded chain inherits.

OB-3's prototype is the confluence: it cannot be written until State + Turn land, but its
TARGET is fixed now, so those lanes build toward a known encoding rather than a guess.

## 4. Next action (when State + Turn land)

Author `Loom/ReceiptClaim.lean` statement-first: the CRS-claim-of-a-turn as a `def`, with
the four PASS obligations (a)-(d) as keystone-fielded statements (satisfiable + teeth built,
per the audit lesson), then fan out the proofs. If (c) or the seam (4) will not close
linearly, STOP and surface it as the OB-3 finding — that is the checkpoint doing its job.
