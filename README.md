# minidregg

**A Lean-first semantic kernel and proof system, built at AI speed under
instruments designed on the assumption that AI-scale proving fails silently.**

**Project site:** [emberian.github.io/minidregg](https://emberian.github.io/minidregg/)
· architecture: [`PROJECT.md`](PROJECT.md) · laws: [`ATLAS.md`](ATLAS.md) ·
evidence ledger: [`GOAL.md`](GOAL.md)

This tree is roughly three weeks old. It contains 420 Lean files; its proof
system, **Selvage** (`Selvage/`, 96 files, ~48K lines), carries **zero
`sorry`, zero `axiom` declarations**, and every `#print axioms` in the tree is
`#guard_msgs`-pinned, so an axiom regression fails the build rather than
printing into a log nobody reads. The whole tree builds green (3,421 jobs).
Those facts are cheap to state and cheap to check; the interesting part is
the discipline that makes them mean something.

## The problem this repo takes seriously: green is not true

Machine-checked developments fail in ways the kernel cannot see: a soundness
theorem quantified over a type nothing inhabits; a bridge hypothesis that
mis-states what the unmodeled half does; a bound proved "explicit" but never
exhibited below 1; a spec that hypothesizes exactly the gap that is the bug.
These are not hypothetical failure classes — each has occurred in shipped,
peer-reviewed verification work across the ecosystem, our own included. At
AI-assisted proving speed, they are the *dominant* failure mode: the prover
never tires of producing green things.

minidregg's answer is to make vacuity **mechanically detectable**, and to
treat every safeguard as itself needing a demonstration that it can fire:

- **Statement-first, with refutation teeth.** Every keystone theorem ships
  with a satisfying witness *and* a falsifying case showing its hypotheses
  are constraints — an inhabitation theorem alone is satisfied by a carrier
  that does nothing. Where a bound is claimed sharp, the tree exhibits the
  adversary attaining it (e.g. the light-client proximity error
  `(⌊δ·n⌋+1)/|F|` is proved *and attained* by a landed example).
- **A carrier census** (`scripts/CarrierCensus.lean`): a mechanized
  environment query for types that are quantified over somewhere and
  constructed nowhere — the signature of vacuous quantification. It found
  four provably-uninhabitable cell schemas in this tree (we then proved the
  emptiness: a materializer exists **iff** the state space is countable, and
  the deleted total-function carrier wasn't). The census self-tests against
  carriers whose status is known by construction, because an instrument that
  silently stops detecting looks exactly like a clean tree.
- **Premise inhabitation as a deliverable.** "The theorem is conditional on
  H" is acceptable only with either a witness for H or a named, tracked
  obligation. Several of this tree's results exist precisely to close
  premises other developments carry silently.
- **No `#guard` unit tests in proofs.** A fact worth asserting is worth
  naming: `theorem` + `decide`/`rfl` + a pinned axiom footprint. `#guard` is
  a compiled evaluation with the name, term, and axiom record deleted.
- **Lean authors the artifacts.** Constraint systems, descriptors, and
  protocol data are *emitted from Lean* and consumed by Rust; Rust is
  generated glue or opaque fallible computation, never a semantics. A
  hand-written model "of" an implementation is a twin, and twins drift — the
  emit pipeline makes the checked object and the deployed object the same
  object. (`Compiler/Emit.lean` → JSON descriptors → the native side
  `include_str!`s them; drift is a CI failure.)

If you build verification tooling: the instruments are the part of this repo
we most want challenged.

## Selvage

Selvage is the proof-system layer: hash-based, small-field, post-quantum in
its assumptions, and aimed at the **compilation half of the SNARK stack** —
the layer between "an interactive protocol is round-by-round sound" and "a
deployed non-interactive verifier accepts only true things," which is where
published soundness analyses most often stop. In the tree today, sorry-free:

- **FRI/Reed–Solomon proximity** with exact, attained error bounds at the
  unique-decoding threshold; regime interfaces (`JohnsonRegime`,
  `HalfThresholdRegime`) tracking the 2025–26 proximity-gap literature,
  including the refutations — conjectured legs are *named hypotheses*, never
  silent.
- **Correlated agreement** machinery, and the seams to consume external CA
  results as they are mechanized.
- **A light-client soundness suite** (`LightClientSound`, `…FS`,
  `…Grinding`): commit-then-sample verification with the Fiat–Shamir
  transport and a grinding bound whose try-count factor is proved
  *necessary* — the two-candidate grinder that beats the fixed-chain bound
  is exhibited, not assumed away.
- **The RBR→Fiat–Shamir compiler theorem** (`fsKeystone`): `(t+k)·ε_rbr`,
  unconditional, over an *inhabited* lazy-sampling random-oracle handler
  rather than an axiomatized one.
- **BCS-style transform soundness at the deployed alphabet** — roots,
  opened columns, opening proofs — with erasure-correction extractors, plus
  state-restoration soundness. To our knowledge no other mechanized
  development has these; they are roadmap items or stubs elsewhere.
- **Accumulation-scheme depth composition** (`Selvage/Depth.lean`): the
  hash-based accumulation depth theorem machine-checked — including a proof
  that the published theorem's literal statement **fails at a corner case**
  (`OB2_depth_composition_false`), with the one-guard repair. Mechanization
  that only ever confirms the paper is not earning its keep.
- **Sponge indifferentiability** (the `SpongeIndiff*` family): to our
  knowledge the only mechanized indifferentiability development outside
  EasyCrypt's CCS'19 SHA-3 proof, and the first in a foundational
  kernel-checked prover. (Honest scope note: indifferentiability alone does
  not close Fiat–Shamir *knowledge* soundness; the extraction-friendly
  strengthening is tracked as an open obligation, not claimed.)
- **A two-sided, parameter-concrete security budget**: the deployed
  configuration's error is proved `≤ 2^-55` *and* `> 2^-56`, with the
  dominant term named. A bound that is merely "explicit" can be vacuously
  loose; a two-sided bound cannot.
- Sumcheck (with an AIR-embeddable verifier), LogUp, additive FRI over
  binary towers, ZK extraction games, and the mixed-field soundness
  accounting (`MixedFieldBudget`) that prices base-vs-extension choices as
  theorems rather than folklore.

**The honest gate, stated plainly:** Selvage is currently theory ahead of
runtime — the accumulation architecture it proves is not yet the one any
deployed prover here runs, and some sharp results are proved at small
domains while the deployed-parameter statements carry named hypotheses. The
per-file docstrings say which is which; `GOAL.md` tracks the distance. We
consider publishing that distance part of the method.

## Relation to the ecosystem

This work is complementary to — and gratefully downstream of — the current
mechanization wave: **ArkLib**'s IOR framework and coding-theory library,
the **S-two AIR verification** (Avigad et al.), **Hirai's** FRI
round-by-round soundness formalization, **VCVio**'s oracle framework, the
**CompPoly** decoders, and the simplified-FRI-RBR line (Garreta–Mohnblatt–
Wagner) written explicitly to enable work like this. The near-term prize we
care most about is *compositional*: the ecosystem now holds proved
unique-decoding correlated agreement, an MCA-conditional FRI-RBR theorem,
and (here) the FS/BCS compilation layer — three trees, no one of which can
produce an unconditional, non-interactive, deployment-parameter FRI
soundness statement alone. Together they can. We are actively building
toward that composition and would rather do it *with* the other trees'
authors than in parallel.

## Where this is going

The severe version of the ambition: **a fully open, post-quantum,
machine-checked path from "a computation ran" to "anyone can verify it
cheaply" — for programs, for ML inference, and ultimately for encrypted
computation** — with every soundness claim either proved two-sided at
deployed parameters or carrying a named, priced, falsifiable hypothesis.
Concretely on the bench: vector-relation proving for the BFV pipeline
already emitted from Lean here; a commit-then-audit sampling theorem (the
economics that make heavyweight proving deployable are a supermartingale
argument away from being a *checked* deployment guarantee, with the error
budget — commitment binding, beacon grindability, checker soundness —
composed into one number, which no deployment currently states); and the
verified-artifact layer for verifiable inference, where the tables and
constraint semantics are proved against mathematical specifications rather
than trusted.

The kernel/medium half of the repo (typed requests, request-indexed
authority, canonical state transitions, hyperdocuments with transclusion and
causal history, the durable/WAL layer with idempotent replay) is the same
construction pointed at systems: receipts instead of unauditable assertions,
for users and agents alike. `PROJECT.md` has the architecture; it is one
object, not a federation of demos.

## Engaging

Everything here is open and intended to stay that way — the position of this
project is that **verifiability is not an enterprise feature**. Issues, mail,
and adversarial readings are all welcome; the most valuable contribution is
a demonstration that one of our theorems is vacuous, because either the
instruments catch it (good) or they gain a new tooth (better).

Build: `lake build Minidregg`. The import boundary
(`scripts/check-import-boundary.sh`) enforces that `Theory/` is
candidate-independent (Mathlib-only) and `Selvage/` sits on `Theory` alone.
Unsigned commits indicate autonomous agent work; the evidence ledger records
exact committed-source replays on independent machines.
