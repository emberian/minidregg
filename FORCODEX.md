# FORCODEX — minidregg handoff, 2026-08-11

## Resumed megaswarm convergence — latest authoritative status

The earlier refresh immediately below was accurate when written, but its five
"next stretches" are now mostly landed.  The resumed swarm constructed the
carriers instead of weakening their statements, integrated the green modules,
and kept physical and cryptographic ceilings explicit.

What is now materially true:

- Durable semantics retain canonical post bytes and read guards, derive exact
  ten-lane authorized charges, frame/checksum WAL records, model torn tails and
  crash repair, and prove intersecting-quorum finality safety and idempotent
  failover.  Reactive terminal races, provider execution leases, and canonical
  escrow deposit/fill/cancel/expiry/refund settle through the same payload-bearing
  intent and exact-charge model.
- Hyperdocuments have concrete linear link publication/reopen witnesses and a
  concrete two-parent conflict merge whose content, causal event, history opening,
  WAL recovery, and quorum-finalized value all agree.  Content, event-history, and
  authority state also have bounded versioned page formats with exact Lean cSHAKE
  roots and one pinned extension catalog.
- The raw Tower256 path is inhabited by concrete PCS levels, statements, an
  opaque-byte reflected verifier, an actual receipt-derived additive execution
  game, and a same-coin raw history/additive four-event join.  The old universally
  binding checkpoint remains a formally impossible regression target, not a
  deployment goal.
- BFV and note-spend control receipts can no longer masquerade as semantic proof
  admission.  Semantic admission requires nonzero exact suite identity plus the
  named same-coin arithmetic/PCS/CR/ROM/PoK laws; current zero-pinned requests are
  proved non-deployable.  The first concrete sealed note-spend cell adapter is now
  inhabited without adding a release channel.
- Credential issue, strict attenuation, use, revocation and epoch rotation now
  run through an exact bounded policy page and a guarded durable debit/retry path.
  Policy/signature soundness and physical storage are still named boundaries.
- The bounded page harness has exact-source hbox and persvati evidence: 420 raw
  samples per host, semantic checks passing, identical encoded-byte/checksum
  columns, and honest Lean-interpreter throughput only.  It is not a native,
  cryptographic, I/O, or end-to-end consumer benchmark.

The latest resumed umbrella pass built `Minidregg` locally at 3,303 jobs.  After
the final integration imports, the carrier census reports 1,210 declared carriers,
510 outside-home producers, 549 raw unwitnessed carriers, five audited
impossible/obsolete targets, and 544 nominally actionable entries.  A
manual top-40 audit found only seven or eight genuinely missing constructions;
most are already-inhabited nested data, explicit conditional security seams, or
legacy carriers the canonical flat-hyperedge path supersedes.

The most important open line is now narrow and user-facing.  One request/result
byte surface is used identically by human and agent origins and proves publish,
lost-response crash, recovery, retry, and exact reopen.  The remaining weld is the
accepted semantic posts to exact bounded-page deltas/cSHAKE roots plus a real
transactional filesystem/database implementation and a client that actually uses
the endpoint.  Until then, link publication/recovery is S/A rather than D.  Real fsync/OS/device
refinement, authenticated network votes, replication liveness, concrete PCS/CR/ROM
prices, production proof suites, client cutover, and end-to-end tail benchmarks
remain open.

## Historical: first Codex integration refresh — later on 2026-08-11

The handoff below was exactly the right warning at `25d2a5a`, but it is now a
historical diagnosis rather than current status.  The follow-up swarm did not
paper over the empty carriers; it changed the representations, built witnesses,
and retained the impossibility results as regression teeth.

What changed:

- `CellState.LogicalState` now uses one canonical dependent finite map.  The four
  deployed schema materializers and cells are exhibited (`83d889f`, `e5ccb49`),
  with the old total-function cardinality obstruction retained as a theorem.
- The Hyperdocument causal layer is no longer unexplored: a real semantic family,
  accepted genesis/append path, and canonical authority projection landed in
  `430d591` and `c15d2a3`.
- Policy selection is committed by authority state.  `AuthState` binds a policy
  root/address, authorization retains exact membership/address evidence, the
  compiler derives the committed `PredCompile` path, and generated artifacts were
  refreshed (`9faa3cf`, `47d9e4c`, `54e331c`).
- The old `SemanticHistoryTower256CheckpointGame.JointGameFamily` is **not an
  inhabitation target**.  `62c0997` proves it impossible at every positive Merkle
  height: completeness plus universal `PositionBinding` would inject more words
  into the 256-bit cSHAKE root range than that range can contain.  The honest
  replacement is the raw path in `384b1bd`, which retains equivocation and gives a
  same-coin four-event ledger with extracted collision and transport obligations.
- Kernel semantics grew actual frontiers rather than more callbacks: canonical
  resource effects (`4119cf4`), durable payload/read-guard intents (`d8d4e53`),
  authority-guarded Hyperdocument commit (`deebdbb`), fee-first admission
  (`c3854a6`), heterogeneous cell lifecycle (`604a3ca`), scoped history projection
  (`b4a4866`), and an executable two-leg declared-hyperedge-to-typed bridge
  (`8e84438`).

Current verification: local `lake build Minidregg` is green at 3,264 jobs;
import-boundary, carrier-census self-test, and `git diff --check` are green.  Exact
committed-source remote replays are recorded in the evidence ledger; production
cryptography, physical storage refinement, and consumer cutover remain explicit.

The highest-value next stretches are now:

1. instantiate the raw proof/controller path with concrete executable verifier,
   transcript transport, and priced cSHAKE/PCS/ROM events;
2. join reactive finalization to durable settlement with a canonical terminal
   promise cell and race/exclusivity semantics;
3. exhibit a real two-parent Hyperdocument merge/publication and then cut over one
   user/agent workflow end to end;
4. refine durable payload/WAL semantics into a framed physical implementation with
   torn-write recovery, replication/finality, and liveness stated separately; and
5. replace existence codecs/roots with versioned deployed codecs and cryptographic
   binding, without weakening the semantic constructions they currently witness.

Everything below remains useful as the original fault report and as a record of the
traps that found the bugs.  Read its present-tense status claims as applying to the
tree named in its opening paragraph.

Written by claude at the end of a long 08-10 session. Not a status report: the
things here are the ones that will change what you do, in the order they'll
change it. `GOAL.md` has the full trail; `ATLAS.md` still has the sixteen laws
and is unchanged.

Tree state at handoff: `25d2a5a` (mine) under `e9c7f3a` (ember's Pages site).
`lake build Minidregg` green at 3245 jobs, import boundary green, 861 pinned
axiom footprints, zero bare `#print axioms`, zero `sorry`. 289 Lean files,
128,209 lines.

---

## 1. Read this before you believe any theorem about a cell

**Every `CellState.Materializer` in this tree is provably empty**, at all four
schemas: `CredentialAuthorityState.schema`, `Hyperdocument.cellSchema`,
`HyperdocumentEventLog.cellSchema`, and `DeclaredTurn.effectSchema`. The proofs
are in `Theory/MaterializerCardinality.lean` and
`Kernel/EventLogMaterializerLimit.lean`.

The argument is three lines. A materializer carries `LawfulCodec (LogicalState
S)`; `decode_encode` makes `encode` injective; so a materializer is an injection
from the schema's entire state space into `List UInt8`, which is countable. Each
schema has infinitely many two-valued fields, so its state space is not.

Consequence: **every theorem quantified over a `Materialized` cell at a deployed
schema is vacuously true.** Credential issuance, attenuation, revocation, epoch
rotation; the whole Hyperdocument operations layer; the atomic two-cell
publication; the flat multi-incidence turn. Nothing is *false*. Nothing was
*checked* either, and vacuous theorems read exactly like real ones — which is
why this survived a year.

If you touch anything downstream of a cell, that is the fact to hold. The two
schema modules say it in their own headers now, and `README.md` / `PROJECT.md`
no longer claim maturity for those layers.

## 2. The instrument that would have caught it — use it

`scripts/check-carrier-census.sh` (wrapping `scripts/CarrierCensus.lean`) walks
the environment and answers: *which carriers are quantified over somewhere and
produced nowhere outside their own defining module?*

Today: 974 carriers, 338 produced outside home, 112 skipped as trivially
inhabited, **521 unwitnessed and load-bearing**, ranked by how many declarations
quantify over each. The ranking is the product; the raw list is a dump.

```
246  CredentialAuthorityState.ProjectionUniverse
224  CausalVersionDag.SemanticFamily        <- nobody has looked at this layer
206  CausalVersionDag.Anchor
182  DeclaredHyperedge.Declaration
161  Tower256AdditiveFriController.MerklePcs
133  HyperdocumentOperations.Config
 92  HyperdocumentOperations.Accepted
 68  SemanticHistoryTower256CheckpointGame.JointGameFamily
```

Three things about it you need:

- **It is a reachability query, not a proof of emptiness.** An unwitnessed
  carrier may be perfectly inhabitable and merely unbuilt. `JointGameFamily` is
  probably that. The four materializers needed a separate emptiness proof, and
  that is still the only way to *know*.
- **It has its own teeth.** `selfTest` pins six carriers whose answer is known
  by construction and fails the run if any flips. A census that quietly stopped
  detecting would otherwise look exactly like a clean tree.
- **The wrapper fails on a broken instrument, never on the count.** 521 is
  today's honest number, not a threshold. Gating it would reward hiding
  carriers instead of witnessing them.

Companion discipline, already enforced: every `#print axioms` in the tree is
`#guard_msgs`-pinned, so an axiom regression fails the build rather than
printing a different list into a log nobody reads. Use
`#guard_msgs (whitespace := lax) in` — Lean wraps the axiom list for long
declaration names and a strict pin passes for short names while failing for
long ones.

## 3. In flight: the `LogicalState` migration

ember chose the design on 08-10: **Option-valued sparse encoding as the
primitive**, with schema-side and state-side defaults *derived* on top as views
rather than as rival cores. Her framing, and it's the right one — there is
nothing to choose.

Landed:

- `Theory/SparseLogicalState.lean` — `SparseState` with `read` (Option-valued)
  and `readD` (takes a default, gives either convention). `readD_empty` proves
  "no default" and "default everywhere" are one object seen two ways.
  `nonempty_lawfulCodec_sparse_effect` carries it to an actual codec for
  `DeclaredTurn.effectSchema`, the schema proved empty as a total function.
- `Theory/StoreFiniteSupport.lean` — the boundary invariant. Scoping changed the
  step's shape: `EffectDeclaration.Store` has 113 references but only **20**
  cross into materialization, and the other 93 are semantics, which needs no
  codec. So the store stays a total function where it does semantics, and
  finite support is required exactly at the boundary. `sparseOfStore_readD` is
  the faithfulness theorem: read the sparse state back with the zero default and
  you get the original store at every key.

**Remaining for step 1, mechanical:** point `DeclaredTurn`'s materialization at
`sparseOfStore`, thread `finitelySupported_ofZero` through the 20 boundary
callers, switch `effectSchema`'s cell to `SparseState`.

**Steps 2–4** are the other three schemas, in the order and with the reasoning
written into `SparseLogicalState.lean`'s footer. Each needs a
`Countable (Sigma S.FieldType)` instance that does not exist yet — `Countable
AuthorityField` alone wants a `deriving instance`, and the capability value
types reach `Countable` through `Finset`. That plumbing is part of the step, not
a precondition someone else supplies.

`materializer_nonempty_iff_countable` means there is exactly one criterion:
whatever replaces the total function is correct **iff** it lands in a countable
type. The refactor cannot fail for a subtle reason.

**This is a staged migration with a named endpoint: deletion of the
total-function field in `CellState.LogicalState`.** It is a deliberate temporary
twin. If you find yourself extending both shapes, stop — that is the state the
endpoint exists to prevent.

## 4. Traps that cost me hours

- **Tailscale lies about the build boxes.** It reported hbox offline 15d and
  persvati 42d while both were up (25 and 31 days) and reachable over plain
  `ssh hbox` / `ssh persvati` on mDNS. The `QUIESCELOG` blamed a missing
  persvati replay on `NeedsLogin` for weeks; nobody had tried the front door.
  There is now one persvati replay:
  `E-20260810T201633-25551-persvati-9d61e61aa1f1-lake`, all exits 0.
- **hbox is yours and minidregg stayed off it.** At handoff it was load 22.5 on
  24 cores, 96 of 123 GiB, 38 sessions. Everything remote went to persvati. If
  datacake is not supposed to be that hot, that is worth a look independently.
- **A stale `.olean` manufactures a RED, not just a green.** `lake env lean` on
  an edited file writes no olean, so an importing file silently loads the
  previous version. I spent several cycles convinced a canonical post-root
  refused to move; the witness was right and the cache was old. `lake build
  <Module>` first, then re-check.
- **Grep the TYPE, not the names you expect.** I built a byte-codec toolkit in
  `Theory/` on the claim the repo had two lawful codecs. It has a complete and
  better one — `Compiler.Tower256ConcreteBackend.StreamCodec`, a prefix codec
  with the append law, `xmap`/`product`/`sum`/`list`/`nat` in base-255. I had
  grepped for five spellings I expected and confirmed my own expectation.
  Reverted in `6efe4f3`; the request/Action/Declaration codecs were rebuilt on
  `StreamCodec` in `Compiler/`, where byte transport belongs.
- **Section `variable`s silently swallow declarations.** In one module a
  `variable (transcript : ...)` followed by `structure`/`def`s produced
  "unused variable" warnings and the declarations never entered the
  environment, with no error. Explicit binders per declaration fixed it. If a
  `#check` says a name you just defined is unknown, suspect this before
  suspecting yourself.

## 5. What is actually open, ranked

1. **The census's top entries.** `CausalVersionDag.SemanticFamily` (224) and
   `Anchor` (206) are a layer nobody has examined; they were the census earning
   its keep on its first run. Check whether they are unbuilt-but-inhabitable or
   another `MaterializerCardinality`.
2. **Migration step 1's mechanical remainder**, then steps 2–4.
3. **`JointGameFamily`** — defined in one file, consumed in two, constructed
   nowhere, so the four-event end-to-end price is conditional on a carrier
   nobody has built. Unlike the materializers this is *unexhibited*, not proved
   empty, and its fields look inhabitable.
4. `QUIESCELOG.md` resume item 5 (cut over one user/agent workflow) is
   **blocked**, and the block is item 1 of this list: the workflow's cells are
   uninhabitable until the migration lands.

## 6. Conventions worth keeping

- `scripts/local-check.sh HEAD -- lake build Minidregg` for isolated
  committed-source evidence; `scripts/remote-check.sh persvati HEAD -- ...` for
  cross-machine. The remote schema has **no** `dependencyIntegrityExit` — it
  pins the seed by revision manifest and a run-private tree — so don't quote it
  as the local runner's third exit code.
- Witnesses carry refutations. Every witness added on 08-10 ships teeth showing
  its equations are constraints, because an inhabitation theorem alone is
  satisfied by a carrier that does nothing.
- Commit named pathsets, never `git add -A`; prose messages via `git commit -F`
  (backticks in `-m` get command-substituted by zsh).
- Unsigned commits are expected while working autonomously.

---

One editorial note, since it shaped everything above. The best result of the
session did not come from proving something — it came from trying to *build*
something and failing. Four emptiness proofs and a census fell out of one failed
attempt at a witness. The corresponding smell: if a construction feels
unreasonably hard, ask whether it is *possible* before assuming you are bad at
it.
