# Loom vs Plonky3 — the defensibility brief

*For the conversation that starts with a raised eyebrow. Written to be handed to a skeptical
peer, so it quotes the pessimistic numbers and names what we give up. If this doc can't
survive that reader, the decision can't either. Status 2026-08-07: Loom's v0 SOUNDNESS TOWER
is proved (machine-checked, hand-audited) — the whole-history-aggregation promise is a Lean
term — but there is still NO prover and performance is UNMEASURED; read §6 (honest state)
before §3.*

## 0. The one honest sentence

**We are not claiming a better SNARK; we are claiming a different *contract*: a proof system
whose soundness is a machine-checked Lean term, whose statements are our kernel's own
algebra (not a VM that simulates it), and whose whole-history aggregation is a theorem at
deployed depth — accepting, in exchange, that we give up a mature, audited, fast,
ecosystem-supported prover and take on multi-quarter engineering + research risk.**

If that trade isn't worth it for a given deployment, the answer is: stay on Plonky3. This
doc exists so that answer is made on the real numbers, not reflex either way.

## 1. What Plonky3 is, stated fairly (it is excellent)

Plonky3 is a production STARK toolkit: FRI-based, small-field (BabyBear/KoalaBear), fast
recursive proving, real deployments (SP1, Valida, others), an active ecosystem, and years
of engineering hardening. Its verifier is battle-exercised; its performance is state of the
art; its arithmetization tooling (AIRs) is mature. **For proving a fixed computation fast,
today, with support, it is the right tool and Loom is not a competitor to it on those axes.**

What it does NOT give — and these are structural, not maturity gaps:
- Its soundness is a *paper argument + an unaudited-or-internally-audited config*, not a
  mechanized proof. (Our own breadstuffs audit found its predecessor's soundness floor was
  `StarkSound` — a hypothesis with **zero instances** — and its deployed FRI parameters
  quoted a **conjectured** 130-bit bound whose conjecture family was **disproved Nov 2025**;
  the *proven* number was 73-bit. This is not a Plonky3 defect specifically — it is the
  state of the transparent-STARK art: proven-vs-conjectured soundness is the least-reported,
  most load-bearing axis, per the 2026 SoK.)
- Its statements are AIR constraints you hand-author (or generate) and keep in sync with your
  semantics — a gap our own history shows drifts (breadstuffs: 271K lines of hand emission,
  a prover partition, a per-effect weld universe).
- Its recursion is real but its *knowledge-soundness at polynomial depth* inherits the
  rewinding-vs-straightline question (§3).

## 2. Why we are even asking (the forcing function)

minidregg's product IS whole-history aggregation: a light client holding one aggregate learns
that every turn in a federation's history was authorized, conservative, and correctly
committed — re-executing nothing. That sentence is paper2's opening line, and it is currently
**false everywhere it is claimed**, because:

1. **The depth wound.** Every rewinding-based recursion — Pickles, Nova, HyperNova, ProtoStar,
   and the STARK recursion Plonky3 uses in the standard analysis — has knowledge soundness
   *proven only at constant/log depth*. Polynomial depth (= whole history) needs either the
   Extended AGM (an **uninhabited** idealization) or the osROM (strictly stronger than ROM). A
   Nova-style scheme forgeable at poly depth while satisfying the standard definition has been
   *constructed* (eprint 2024/232). So "verify the whole history" is, at deployed depth, a
   heuristic in every off-the-shelf option.
2. **The simulation tax.** Proving our semantics via a general prover means arithmetizing an
   executor (or a zkVM running it) — the thing that drifts, and in the zkVM case a 10³–10⁶×
   overhead to prove a CPU that proves our rules.

Loom exists to make (1) a *theorem* and (2) *unnecessary*.

## 3. What Loom gives that is structural, not just "ours"

- **Unbounded-depth aggregation as a proven theorem.** Straightline extraction (WARP/Arc
  shape: erasure correction, no rewinding) composes depth *additively* by union bound. The
  light-client-verifies-whole-history property holds at the depth we deploy, as a Lean term,
  not a heuristic. No rewinding-based system offers this at our use case; it is the single
  sharpest differentiator.
- **Soundness is a Lean term, not an audit.** Nobody has a fully mechanized soundness proof
  of a complete succinct argument (ArkLib, the serious attempt, is ~293 sorries and aims to
  verify *others'* systems). Loom's own end-to-end soundness is the deliverable, under a
  discipline that refuses vacuity — which already *refuted* our first depth-composition
  statement (machine-checked false at an empty-index corner) and *found a typo in the
  EUROCRYPT WHIR paper* while building a witness.
- **Receipt-native statements.** The accumulated object IS the kernel's turn algebra (OB-3,
  landed at the binding level: the receipt word IS the accumulator's committed codeword). No
  VM, no simulation tax, and the arithmetization is *derived* from one source (N3, landed:
  the compiler is a fold, so circuit⟺executor agreement is free by initiality — the drift
  that produced 271K hand-lines is structurally impossible).
- **An honest, inhabited floor.** Two named carriers: proximity/MCA at *proven*
  (Johnson/unique-decoding) parameters + one ROM realization. Zero capacity conjectures (the
  falsified ones). Everything else is a theorem. No `StarkSound`-with-zero-instances.
- **PQ-plausible, transparent, no trusted setup, no curves, small fields.** Shared with the
  modern hash-based line — a stance, not an invention.

## 4. What we give up (the pessimistic column — read this twice)

- **Maturity.** Plonky3 is years-hardened and deployed; Loom is weeks old and unproven in
  production. This is the biggest real cost and no amount of theory buys it back quickly.
- **Performance is UNMEASURED.** We have not benchmarked a Loom prover — there isn't one yet.
  The honest-parameter stance (Johnson-regime, not capacity) costs ~2–4× prover vs the (now
  falsified) conjectured rates. Loom could be slower than Plonky3 in practice; we do not know,
  and claiming otherwise would be the flattering-number sin.
- **Audit surface & ecosystem.** Plonky3 has external eyes, tooling, hiring pool. Loom has us.
  The mechanized proof is a *different kind* of assurance, not a replacement for adversarial
  external review of the implementation and the deployed field arithmetic.
- **Engineering cost.** A production Loom (prover + verifier + the mechanized tower) is a
  multi-quarter effort even at our demonstrated velocity, with genuine research risk in the
  open slots (OB-4 ZK, OB-2a, small-field linearity).
- **The math is borrowed; the composition is the bet.** The cryptography (WARP, Arc, sumcheck,
  WHIR, RS proximity) is not ours. Our contribution is the *composition* + its mechanization +
  four open research slots. If a slot proves intractable, that's a real failure mode.

## 5. Resource estimate (order-of-magnitude, honest)

- **The mechanized soundness tower** (the differentiator): calibration point — a full FRI RBR
  soundness mechanization was one person / ~6 weeks / 4K lines (simple-rbr-fri). Loom's tower
  (WHIR-at-UD + accumulator + whole-stack straightline apex + FS/BCS) is bigger; at our
  swarm velocity, *weeks-to-a-couple-months* of focused lanes for a v0 tower, longer for the
  Johnson-regime MCA and the ZK slot. The tree today is a spine of ~10 audited keystones.
- **A working prover/verifier** (the engineering): unestimated — this is the larger, riskier
  half, and the one where Plonky3's years are hardest to replace. A credible plan stages it:
  mechanized soundness + a reference (possibly slow) prover first, performance work second.
- **The off-ramp is cheap:** the descriptor/claim interface is ours regardless, so a Loom that
  stalls can fall back to emitting to a Plonky3-style backend without re-architecting the
  kernel. We are not betting the kernel on the proof system.

## 6. Honest state today (do not oversell)

**The v0 SOUNDNESS TOWER is proved** — machine-checked, every keystone on the ATLAS axiom
triple `[propext, Classical.choice, Quot.sound]`, each one hand-audited (statement read, not
just "it compiled") with a built non-vacuity witness and, where it applies, the *false*
statement kept compiling beside the true one:

- **OB-2** — whole-stack straightline depth composition — PROVED (the theorem whose absence
  was breadstuffs' laundered `EngineSound`; anti-weakening check passes).
- **OB-3** — the receipt is native to the accumulator (binding *and* fold) — PROVED.
- **ACC-sound** — the γ-fold's soundness bounds are theorems (`err⋆(δ)+1/|F|` at unique
  decoding, mutual-correlated-agreement genuinely consumed) — PROVED.
- **LC-sound** — the light client's probabilistic soundness: one sampled challenge schedule
  catches a false history except with prob `≤ n·(err⋆(δ)+1/|F|)` (exact-word form sharp at
  `1/|F|`) — PROVED, and the naive one-fixed-schedule form is machine-checked FALSE beside it.
- **Decider** — the one-time final check, cost `r+1` regardless of chain depth — PROVED.
- Under them: the code layer (Reed-Solomon Cor 4.11 + MCA-at-UD, constrained code + γ-batching,
  out-of-domain uniqueness), the sumcheck front (retiring the constraint channel), and the
  Fiat-Shamir/ROM transcript layer (inhabited handler, keystone unconditional).

So the central promise — *one aggregate proves the whole history, sound at deployed depth* —
is now a chain of Lean terms, not a heuristic. **What that claim does NOT yet include, stated
plainly:** the schedule is proved sound as a *uniform* sample; deriving it from a Fiat-Shamir
hash is `[LC-sound-fs]` (rides the landed FS layer). Soundness is proved against claim-*
satisfiability; binding a *forging prover*'s recommitments (straightline extraction) is
`[ACC-extract]`. The decider checks *exact* membership; the rate<1 proximity test (the WHIR
low-degree test) is in flight, and with it `[OB3-c-prox]`/`[DEC-proximity]`. ZK is a hiding
*shell* + its MDS opening-core; the full opening-leakage proof is `[OB-4-hiding-rbr]`, the
contribution slot. And — unchanged and load-bearing — **there is still no prover, no verifier
implementation, and no benchmarks; performance remains UNMEASURED** (§4). This is a proved
soundness tower with a deployment layer in progress, not a system you can prove a block with
tomorrow — but it is no longer an "early spine," and the promise it was built to make is kept.

## 7. The decision criterion (when Loom, when Plonky3)

- **Stay on Plonky3** if: you need to prove a fixed computation fast, now, with support; you
  do not need whole-history aggregation with proven-depth soundness; the simulation tax is
  acceptable; mechanized soundness is not a requirement.
- **Pursue Loom** if: the product *is* unbounded-depth aggregation and "the light client
  learns the whole history" must be true rather than heuristic; a machine-checked soundness
  floor is a differentiator worth a research bet; receipt-native (no VM) statements matter;
  PQ-transparency at proven parameters is required; and you can fund a multi-quarter effort
  with a Plonky3 off-ramp.

**The defensible pitch to a peer, in one breath:** *"We're not replacing Plonky3 because we
think we can out-engineer it on speed. We're building Loom because our product's core promise
— one aggregate proves the whole history — is a theorem in no existing system at deployed
depth, and because a capability computer's soundness should be a proof you can read, not an
audit you have to trust. It's an early research spine with a real off-ramp, and here's exactly
what it costs and where it can fail."*
