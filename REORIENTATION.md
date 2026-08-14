# Reorientation — 2026-08-13

This is a thin cross-repository orientation note, not another evidence ledger.
For research conclusions, `~/dev/zkml-research/docs/VERDICTS.md` is the single
current-truth file.  For exact proof/build evidence, use each repository's own
ledger at the commit being claimed.

Snapshot inspected while writing this note:

- `minidregg` `9b1d512` on `main`, with independently owned zkML-matmul and
  Uwueave projection work in the shared worktree;
- `zkml-research` `a42c9b9` on `dev`, with `vendor/` untracked; and
- `lean-uwueave` `49203f1` on `dev`, with active trust/debt/runtime work.

The snapshot is an ownership marker, not a claim that later commits are stale.

## One system, four responsibilities

The project is a **receipts-native compute fabric**: every accepted turn is a
typed, authorized semantic state transition whose evidence is carried now or
committed for a precisely priced audit later.

The repositories/layers have different authority:

1. **Uwueave / Preoscript chooses the coordination shape.** It describes
   partial results, guarded data, futures, CRDT-safe work, escalation seams,
   plans, and budgets. Its projections are checked planning data. They are not
   authorization, a scheduling permit, or semantic acceptance.
2. **minidregg owns meaning.** The kernel owns the exact request, authority,
   pre-state, effect, resource law, canonical post-state, receipt, and history.
   Native code may propose bytes or fail; it never returns the acceptance bit.
3. **Selvage owns proof/audit compilation.** It connects round-by-round
   protocol claims to commitments, Fiat--Shamir/BCS, accumulation, sampling,
   and explicit failure budgets. A green theorem is useful only when its
   carriers run and its cryptographic/deployment legs are named or inhabited.
4. **zkml-research owns protocol selection by evidence.** It measures candidate
   designs, records refutations, and decides which statements are worth moving
   into the checked stack. It is not a second semantic kernel or proof tree.

The narrow interfaces should therefore be:

```text
Preoscript checked plan/data
          |
          v
minidregg exact request + authority + state transition
          |
          v
typed computation statement + canonical commitments/openings
          |
          v
Selvage proof or commit-and-audit evidence
          |
          v
minidregg receipt + durable causal history
```

Every crossing must pin a format/version, source identity, and exact claim
ceiling. No crossing may silently promote data into authority or a host test
into semantic/cryptographic evidence.

## First vertical slice

Build **one authorized, audited exact linear-layer turn** end to end.

The slice binds one model/version and real field encoding, one typed input and
claimed output, one contraction statement, one audit/proof policy, and one
resource/disclosure plan. Preoscript supplies checked planning and escalation
data; minidregg authorizes the exact request and derives the receipt; the zkML
relation supplies the exact matmul/contraction semantics; Selvage supplies the
opening/checker and composed audit budget; the durable path appends and reopens
the same canonical receipt.

The success criterion is deliberately narrow:

- the exact accepted computation is stated in Lean and has positive and
  adjacent-refusal witnesses;
- native execution returns only candidate data/proof bytes or an error;
- model/weight binding uses a proof-openable Poseidon2 field encoding and
  layout, not a host SHA checksum described as a registry commitment;
- the checker, commitment binding, beacon/grinding, and Fiat--Shamir terms are
  instantiated or remain explicit zero-suite deployment blockers;
- the Preoscript artifact is consumed as plan data and rebound to the kernel's
  exact request rather than trusted as a permit;
- the receipt survives the existing durable reopen/retry path; and
- exact committed-source verification runs remotely on hbox or persvati, not
  as a large build on nextop.

This is not yet a claim about a whole neural network, correct backpropagation,
PQ-128 FHE, physical stable media, or production key custody.

## Immediate convergence order

1. Let the active matmul lane finish its correction from Hadamard product to
   contraction and preserve its explicit padding, PCS, Fiat--Shamir, and
   registry residuals.
2. Replace the accidental Projection-V2 bridge decision with an explicit
   interface choice. Use V3 for rich checked plan/result/certificate data;
   use the V4 sidecar only where context-bound runtime-auth facts are actually
   required. In both cases the imported value remains neutral data.
3. Finish one runnable hash-based multilinear opening seam. Reuse Selvage's
   existing `OpeningScheme`, RBR-to-Fiat--Shamir, BCS, and accumulation cone;
   do not invent a second PCS abstraction merely to look multilinear.
4. Instantiate the audit checker's named transport obligations for the chosen
   contraction statement, then price the real binding and beacon terms.
5. Join that evidence to one canonical computation receipt and the existing
   durable history path. Only after this is green should the slice widen to
   nonlinearities, multiple layers, low-rank training deltas, or encrypted
   computation.

## Things to stop doing for now

- Do not add generic kernel breadth unless the vertical slice consumes it.
- Do not extend the proof-theory cone merely because another clean theorem is
  reachable; prioritize the runnable commitment/checker seam.
- Do not put Plonky3 in the trust path. Its upstream bug fix is still useful
  for differential measurement and for repairing our stale refusal gate.
- Do not migrate to KoalaBear on the current evidence. Keep BabyBear/Ext4 and
  fix the blowup/query configuration honestly.
- Do not start full vFHE integration before the parameter/PQ-security and
  checker-instantiation questions are settled.
- Do not claim the rank-1 gradient check verifies backpropagated `delta`, or
  that it removes the quadratic commitment to a materialized updated matrix.
- Do not treat V2/V3/V4 projection bytes, Rust tests, SQLite/WAL exercises,
  signatures, or hashes as stronger evidence than their owning theorem says.
- Do not run massive proof builds on nextop while the remote builders are
  available.

## The decision rule

Prefer work that shortens the path from a real request to a reopenable receipt.
For every proposed lane ask, in order:

1. Does it make the statement smaller or more exact?
2. Does it instantiate a named trust/security boundary?
3. Does it connect a proved layer to a running consumer?
4. Does it add a refusal tooth or exact reproducible evidence?

If all four answers are no, it is probably not the next thing.
