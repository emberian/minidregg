# minidregg

**A machine-checked proof system, a correct-by-construction AIR compiler, and a proof-native
computer — built as one artifact.**

If you build with Plonky3 (or any STARK/FRI toolkit), you write AIRs in Rust and trust that (a) the
prover implements a sound protocol and (b) your constraints actually pin the relation you meant.
Both are checked by audit and testing. In minidregg, **both are Lean theorems**: the proof
system's soundness is machine-checked, and the constraint systems are *emitted by a compiler whose
circuit reading provably equals its executor reading* — so the two classic soundness-bug sources
(an unsound protocol, an under-constrained circuit) are closed structurally, not caught in review.

The proof system itself, **Loom**, is not a re-skin of Plonky3's FRI STARK: it is *WHIR*-shaped
(Arnon–Chiesa–Fenzi–Yogev) — accumulation over a constrained Reed–Solomon code with mutual
correlated agreement — with a native zero-knowledge argument of knowledge. Its prover *currently*
reuses the deployed BabyBear⁴ FRI fold (which happens to be Plonky3-identical) as a **backend
starting point**, conformance-locked to the verified fold; that backend is being **superseded** by
the Binius additive-FRI substrate we're building, and the security setting pushed past unique
decoding toward the Johnson regime. The GPU compute *follows* the verified constraints; it is a
component we adopt and move beyond, not the system's identity.

---

## What's different from Plonky3

They share a math family (multilinear sumcheck, Reed–Solomon proximity, BabyBear⁴) and — *for now,
at the hot loop only* — the same GPU fold. But Plonky3 is a **FRI STARK toolkit**, while Loom is a
**WHIR-shaped accumulation system with native ZK** — a more advanced protocol, not just a verified
copy. The differences below are about **the protocol**, **where trust lives**, **what the artifact
is**, and **where it's headed**:

| | **Plonky3** (and STARK toolkits generally) | **minidregg** |
|---|---|---|
| **Protocol** | FRI STARK. | **WHIR-shaped accumulation** (constrained Reed–Solomon + mutual correlated agreement) with a **NIZK argument of knowledge** — a different, more advanced protocol. |
| **Soundness** | The Rust prover/verifier is trusted; audited, fuzzed, battle-tested. | The protocol soundness — sumcheck, RS proximity, the accumulator, Fiat–Shamir, the ZK argument — is a **Lean theorem** (`loomV0_holds`, `loom_zk_argument`), on the standard axiom base, hand-audited. |
| **Circuits (AIR)** | Hand-written in Rust. Under-constraining is the #1 soundness-bug class; caught (if caught) by audit. | **Derived from a spec by a compiler**; circuit⟺executor is proved **by initiality** (`eval_agrees_exec`), so an emitted gadget *cannot* diverge from its semantics. Under-constraining is structurally impossible. |
| **Recursion** | Recursive verification as (hand-written, trusted) circuits. | The **whole verifier is arithmetized as one emittable AIR** (`fullVerifier`) with a machine-checked correctness theorem — "a proof verifies a proof" is a statement you can *prove*, not just run. |
| **ZK** | Add-on transforms; hiding is an implementation property. | A **non-interactive zero-knowledge argument of knowledge** is proved (`loom_zk_argument`) — knowledge-soundness *and* perfect ZK coexist, native to hash-based accumulation. |
| **The trusted floor** | "It's a hash-based STARK" — the proximity gap, ROM, and collision-resistance are assumed. | The **same three assumptions, named and inhabited, and being *proved down***: the proximity gap is *proved* hypothesis-free on a macroscopic band and reduced to one classical lemma over the rest of unique decoding; CR reduces to the RO by an explicit adversary; the RO to an ideal permutation. |
| **Scope** | A proving toolkit. | A proving toolkit **plus a semantic computer** — a kernel (turns, receipts, a gated executor with a real FFI export), a derivation engine, a policy algebra. You build *on* it. |
| **Prover backend** | The reference implementation. | An *unverified* Rust/WGSL crate that adopts the deployed GPU fold **as a current starting point**, proven **bit-for-bit equal to the verified fold** — same speed, verified constraints. Being superseded by the additive-FRI backend. |
| **Trajectory** | Mature, stable, FRI-based. | Actively moving *past* the shared baseline: **Binius binary-tower / additive-FRI** (a faster GF(2) field substrate), the **Johnson/list-decoding regime** (better rates), full-rate proximity. |
| **Line count** | — | ~10% of the system it reimplements; the shrink comes from *deriving* what others hand-write. |

**What minidregg is *not*:** it is not faster than Plonky3, not more feature-complete as a
production prover, and it runs at **unique decoding** (a conservative rate — roughly 2–4× more
queries than the aggressive Johnson/conjectured regime deployed systems use) so that every quoted
number is a *proven* parameter, not a conjecture. It trades peak performance and breadth for
**assurance** and a **verified application substrate**.

## Why you'd use it

- **You cannot afford a circuit bug.** For high-value logic — money, governance, fleet coordination
  — the "my AIR doesn't match my intent" failure mode is eliminated *by construction*: the
  constraints come out of a compiler with a machine-checked circuit⟺executor theorem, and the
  proof system verifying them is itself proved sound.
- **You're building an application, not just proving statements.** minidregg is a proof-*native*
  computer: a kernel with turns, receipts, and a fail-closed authority gate (compiled to a real C
  entry point), a derivation engine where a new effect is a *declaration*, and a policy algebra —
  a verified substrate to build things like fleet coordination on, not just a proving library.
- **You want a number, not a vibe.** The end-to-end soundness is *one proven bound* —
  `≤ 2⁻⁵⁵` at deployed BabyBear⁴ parameters (exact integer arithmetic, union-bounded from proven
  terms), with the dominant term identified. A machine-checked security level, not an estimate.
- **You want a small, explicit trusted base.** The floor is three named, inhabited cryptographic
  assumptions with proof routes — and the load-bearing one (the proximity gap) is *partially
  proved*, not asserted. The trusted base is smaller and legible, not "trust the STARK."
- **Without leaving the deployed performance path.** The hot loop is the same GPU BabyBear⁴ fold,
  adopted into our crate and conformance-locked to the verified fold — assurance rides *on top of*
  the real compute, it doesn't replace it with something slow and academic.

## Feature set

**Proved (Lean, hand-audited):** multilinear sumcheck with adaptive soundness · Reed–Solomon
proximity/FRI at unique decoding · WHIR-shaped **accumulation with unbounded-depth
knowledge-soundness** · Fiat–Shamir composition with a grinding bound · a **NIZK argument of
knowledge** · a **derived arithmetization compiler** (DSL → degree-≤2 gates → retired by the proven
sumcheck) · gadgets (range, Poseidon2, Merkle) composed into a **sound shielded note-spend** · a
**recursive verifier** as one emittable AIR · a **kernel** (resource algebra, the turn as a
universal object, a 4-leg fail-closed gated executor, a verified FFI export) · a **derivation
engine** (effects as declarations).

**Runs (unverified compute, conformance-matched):** a Rust/WGSL prover — descriptor → trace →
Poseidon2 commit → sumcheck → FRI — with the fold on Metal at **~3× CPU**, every stage conformance-
locked to the verified Lean objects. (Conformance, never "verification": there is no formal
semantics of Rust.)

**In flight / honestly undone:** the general `Pred → constraints` lowering and the effect registry;
CR-from-RO and sponge indifferentiability (the floor consolidation); the Polishchuk–Spielman lemma
(full-rate proximity); the additive-FRI transform for the binary-tower substrate; and the helm
north star (`Distributed/`, `Apps/`). The live tally is in `GOAL.md`.

## Architecture

| Directory | Role |
|---|---|
| `Theory/` | Candidate-independent math (codes, fields, the binary tower). Import-boundary–enforced. |
| `Loom/` | The proof system — sumcheck, RS/proximity/FRI, the accumulator, Fiat–Shamir, the ZK argument. |
| `Compiler/` | The arithmetization — the DSL (`Signature`/`Air`), gadgets, the emit path, the recursive-verifier AIRs. |
| `Kernel/` | The semantic computer — resource algebra, the turn, the gated executor, the FFI seam. |
| `Effects/`, `Pred/` | The derivation engine and the policy algebra. |
| `Assurance/` | Bridges composing the layers into deployment-facing statements (the v0 capstone, the manifest). |
| `prover/` | The unverified Rust/WGSL backend that follows the verified emit. |

## Build

```sh
lake build Minidregg          # the full Lean tree (integration gate)
lake env lean <File>.lean     # iterate a single file, race-free
cd prover && cargo test       # prover conformance suite (GPU tests use Metal, skip cleanly without)
cd prover && cargo run --release --bin fri_fold_bench   # the GPU fold benchmark
```

## Reading order

1. [`ATLAS.md`](ATLAS.md) — the diagnosis, the sixteen design laws (each bought with a documented wound), the architecture carve.
2. [`docs/LOOM-COMPLETE.md`](docs/LOOM-COMPLETE.md) — the skeptic-facing account: proved / floor / remainder.
3. [`Assurance/LoomV0Manifest.lean`](Assurance/LoomV0Manifest.lean) — the machine-checked table of contents (~75 type-checked re-exports).
4. [`docs/PROVER-PLAN.md`](docs/PROVER-PLAN.md) — how the prover adopts the deployed GPU fold into our own crate.

## North star

minidregg is designed to be the substrate under fleet-coordination tools like **helm** — rooms as
cells, posts as signed turns, premises as attested claims, review verdicts and land-receipts as
on-chain receipts. Our own development fleet is the intended first user; every design decision is
tested against *could the helm run on this, better than on what it replaces?*
