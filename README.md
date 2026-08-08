# minidregg

**A proof-native semantic computer, formal-first.**

minidregg is a from-scratch reimplementation of a zero-knowledge accumulation system
([breadstuffs](../breadstuffs)) at **≤10% of its line count** — with the crucial difference that
the parts that matter are *machine-checked theorems in Lean*, not hand-written code. The
arithmetic constraint systems ("AIR"), the proof system, the shielded-transaction logic, and the
kernel's authority gate are all **derived from compilers over formal specifications** — never
hand-authored — so that "the circuit means what the spec says" is a real theorem over the actual
emitted object, not a code review.

It is honest about what it is. What follows separates **what is proved**, **the cryptographic
floor it stands on** (named, inhabited, and being *proved down*), and **what is unverified compute
or unfinished research**. That separation is the point; see [`docs/LOOM-COMPLETE.md`](docs/LOOM-COMPLETE.md)
for the full, skeptic-facing account.

---

## What is proved (machine-checked in Lean, hand-audited)

Every claim below is a Lean theorem on the standard axiom base `{propext, Classical.choice,
Quot.sound}` (many are choice-free), with a *built non-vacuity witness* and, where a claim has a
plausible false neighbor, the false statement kept compiling beside the true one so the true one
means exactly what it says.

**Loom — the owned proof system.**
- **Accumulation + unbounded-depth recursion:** a whole federation history folds into one
  accumulated claim; the extractor recovers every link's witness at arbitrary depth
  (`lightClientKnowledgeSound`), and the tower composes into one capstone (`loomV0_holds`).
- **A non-interactive zero-knowledge argument of knowledge** (`loom_zk_argument`) — completeness,
  knowledge-soundness, perfect zero-knowledge, and Fiat-Shamir composition, native at the deployed
  root/column alphabet. (This was the confirmed-open contribution; the mask counterfactuals the
  extractor needs are *provably* not computable from what the ZK distinguisher sees.)
- **A recursive verifier — a proof verifies a proof.** The entire light-client verifier
  (Fiat-Shamir binding, sumcheck, FRI fold-consistency, Merkle openings) is arithmetized as **one
  emittable AIR** (`fullVerifier`), so verifying a Loom proof *inside* a Loom circuit is a
  machine-checked statement. Its forgery keystone makes collision-resistance *concrete*: the only
  way to cheat is to hit the committed root's hash-collision fiber, exhibited.

**The arithmetization compiler (derived — drift is impossible, not merely avoided).**
- An arithmetization DSL whose circuit reading and executor reading are **equal by initiality**
  (`eval_agrees_exec`) — N3 applied to circuits. Expressions flatten to a degree-≤2 gate system,
  retired by Loom's *proven* sumcheck (`airGateSystem_sound`, linear ∧ quadratic).
- Gadgets, all iff-correct: range, a Poseidon2 hash, Merkle membership — composed into a **sound
  shielded note-spend** (`noteSpend_correct`), which even exhibits a hash collision to make its
  own floor assumption visible.

**The kernel (the semantic computer).** A four-substance resource algebra, the turn as a universal
object (proved a limit at both the agreement and conservation layers), a hidden-witness turn, and a
**gated executor** — `Verb = admission × footprint`, a 4-leg fail-closed gate where the
conservation-breaking verb is unreachable *by construction* — with the **first `@[export]`** and a
verified emitted C symbol, so "the kernel is the executor" is compiled code, not aspiration.

**The derivation engine (`Effects/`).** A new effect is a *declaration*: its IR term, executor,
and serializable descriptor all derive by one function application, agreement and faithfulness free
by initiality. "The derived path is the only path" made concrete.

## Runs (unverified compute, conformance-matched)

The `prover/` crate is a Rust/WGSL prover that **consumes the verified emit** (it never authors a
constraint) and runs the deployed BabyBear⁴ pipeline: descriptor → trace → Poseidon2 commit →
sumcheck → FRI. Its FRI fold is *adopted* (not ported) from the deployed GPU kernel, dispatched on
**Metal**, and runs **~3× CPU** at 2²⁰ elements — while being proven **bit-for-bit equal to Loom's
verified `Proximity.fold`** on conformance vectors. This is a *conformance* target, never called
verification: there is no formal semantics of Rust, so the prover is honest compute *following* the
proofs, not a proof itself.

## The cryptographic floor (named, inhabited, being proved down)

minidregg stands on the **same floor every hash-based SNARK carries** — but treats it as reducible,
not sacred:
- **Proximity gap** — *proved, hypothesis-free*, on a macroscopic band; built end-to-end across the
  rest of unique decoding, reduced to a single named classical lemma (Polishchuk–Spielman).
- **Collision-resistance** — reducible to the random oracle by an explicit birthday-bound adversary
  (in progress).
- **Random oracle** — reducible to an ideal permutation by sponge indifferentiability.

No unproved `axiom` stands in for any of these; each is an inhabited hypothesis with a proof route.
Quoted numbers are proven parameters at unique decoding — no conjectures on the label.

## What is *not* done (honestly)

No production prover or benchmarks beyond the fold; unique-decoding regime (Johnson/list-decoding is
named research); the deployed-ZK adaptive bound reduced to one RO-programming lemma; the additive-FRI
transform for the binary-tower substrate; the effect *registry* and general `Pred → constraints`
compiler in flight; and the **helm north star** (`Distributed/`, `Apps/` — fleet coordination as
the first application) not yet started. The running tally lives in `GOAL.md`.

---

## Architecture (the carve)

| Directory | What it is |
|---|---|
| `Theory/` | Candidate-independent mathematics (codes, fields, the binary tower). Import-boundary–enforced: no dependency on any specific proof system. |
| `Loom/` | The owned proof system — sumcheck, Reed–Solomon, proximity/FRI, the accumulator, Fiat-Shamir, the ZK argument. |
| `Compiler/` | The arithmetization: the DSL (`Signature`/`Air`), the gadgets, the emit path, and the recursive-verifier AIRs. |
| `Kernel/` | The semantic computer — resource algebra, the turn, the gated executor, the FFI seam. |
| `Effects/`, `Pred/` | The derivation engine and the policy algebra (the ATLAS thesis substrate). |
| `Assurance/` | Bridges that compose the layers into deployment-facing statements (the v0 capstone, the manifest). |
| `prover/` | The unverified Rust/WGSL compute backend that follows the verified emit. |

**The laws that bind the work** (each bought with a documented wound; full list in
[`ATLAS.md`](ATLAS.md)): the derived path is the *only* path — nothing is hand-authored beside what
it supersedes; statement-first — a keystone enters as a `Prop` with its satisfiable/teeth/premise
fields before proof work; green + self-reported ≠ verified; quote the pessimistic number in the same
sentence as the claim.

## Build

```sh
lake build Minidregg          # the full Lean tree (the integration gate)
lake env lean <File>.lean     # iterate a single file, race-free
cd prover && cargo test       # the prover conformance suite (GPU tests use Metal, skip cleanly without)
cd prover && cargo run --release --bin fri_fold_bench   # the GPU fold benchmark
```

## Reading order

1. [`ATLAS.md`](ATLAS.md) — the diagnosis, the sixteen design laws, and the architecture carve.
2. [`docs/LOOM-COMPLETE.md`](docs/LOOM-COMPLETE.md) — the honest completion account: proved / floor / remainder.
3. [`Assurance/LoomV0Manifest.lean`](Assurance/LoomV0Manifest.lean) — the machine-checked table of contents (~75 type-checked re-exports).
4. [`docs/PROVER-PLAN.md`](docs/PROVER-PLAN.md) — how the prover adopts the deployed GPU fold into our own crate.

## North star

minidregg is designed to be *suitable as the substrate under fleet-coordination tools like helm* —
rooms as cells, posts as signed turns, premises as attested claims, review verdicts and land-receipts
as receipts on chain. Our own development fleet is the intended first user. Design decisions are
tested against: *could the helm run on this, better than on what it replaces?*
