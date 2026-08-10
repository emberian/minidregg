# QUIESCELOG — 2026-08-10

This is not a release note, proof of completion, or conventional handoff. It is the candid memory
of the long 2026-08-09/10 construction session: what became true, what almost fooled us, what is
still merely an interface, and what we should do first when attention returns.

The active goal had run for roughly 7 hours 40 minutes when quiescence was requested. The goal is
not complete and must not be marked complete. Quiescence means: launch no new substantial work,
let near-green owned work finish, integrate only finished artifacts, preserve exact evidence, and
leave the tree understandable.

## Short verdict

minidregg now has a credible common semantic nucleus and proof-control architecture. It is no
longer just a collection of attractive theorem experiments. The four principal umbrellas at
commit `3f74f63` built together from an immutable archive on hbox: 8,729 jobs, command exit `0`,
source-integrity exit `0`. The complete evidence bundle is committed in `c05204b`.

The architecture is converging on one rule:

> One canonical typed state transition, under one complete request-indexed authority, may collect
> evidence from many native proof/execution dialects, but only Lean assigns meaning and constructs
> acceptance.

That sentence is substantially true at the semantic/admission level. It is not yet true as a
production system. Only clause 406 has a narrow positive deployment seam; no external consumer has
cut over; no physical durable handler refines the model; and the major succinct proof paths still
need concrete security reductions and deployment identities.

## The current conceptual model

The common kernel is no longer the Mina-shaped call forest. A turn is a flat typed hyperedge:

1. canonical typed cells name the only logical pre-state;
2. a complete typed request names subject, target, verb, arguments, effect digest, policy, nonce,
   exact pre-root, and cost context;
3. one request-indexed authorization judgment discharges that exact request;
4. one accepted effect retains mode evidence and one validated typed patch;
5. several heterogeneous cells may join under one apex and aggregate resource law;
6. one canonical post-state/delta and typed receipt are derived, not caller supplied; and
7. heterogeneous receipt families enter one retained semantic history without erasing their
   indexed meanings.

Rust has no operational semantics here. Rust is generated manifest/dispatch data or opaque,
fallible candidate computation. Rust may return bytes or an error. It never returns the semantic
acceptance bit and is never called a refinement of Lean.

Loom is the proof-assurance fabric around that narrow waist. Binary Tower256 work, sparse memory,
prime-field proofs, FHE rings, MPC shares, private relations, and causal history keep native
dialects. They meet through canonical representations/openings, roots-before-challenges control,
typed receipt clauses, and one explicit failure ledger. The proof is the bridge; a fake cast or
handwritten runtime mirror is not.

Hyperdocuments are the first serious candidate medium built on the nucleus: canonical content and
event cells, operation intents, stable ranges, marks/annotations, authenticated transclusion and
backlinks, causal histories, explicit conflicts, ancestry-backed merge bases, atomic logical
publication, and versioned user/agent interface negotiation.

## Strong evidence anchors

- Root integration: `3f74f63` (`root: integrate proof-native system surfaces`).
- Exact integrated hbox replay: `E-20260810T003037-13290-hbox-3f74f634e0e1-lake`.
- Evidence commit: `c05204b`; source before/after manifests are identical.
- Documentation reconciliation: `a9b24df`.
- First byte-backed deployed clause: `7c9067b` (clause 406).
- Raw additive Merkle control and collision event: `7e8857d`, `3e4d9fd`.
- Actual history failure classification: `f39ba67`, `3720ceb`.
- BFV zero-pin deployment barrier: `a822066`.
- Proof-native Hyperdocument agent operation: `83e59af`; exact hbox run
  `E-20260810T011521-61763-hbox-83e59af8a50d-lake`.
- Reactive lifecycle fresh-build repair: `3be19cb`.
- Narrowed cSHAKE build surface: `85dee2a`.
- Local isolated-check runner: `7784de5`, `d84f086`, `f254e93`, `7e571d6`; final clean and
  adversarial E2E gates passed.

The root integrated replay predates the final raw-Merkle, history-event, BFV-controller, cSHAKE
split, and local-runner commits. Those newer modules have targeted hbox evidence, but a new final
umbrella replay should be made only after quiescent imports are settled. Do not silently treat the
`3f74f63` run as evidence for descendants.

The equivalent current-root persvati replay was not run because the local Tailscale client reports
`NeedsLogin`; mDNS reaches persvati but the available key is not authorized. Older persvati runs
remain evidence only for their exact commits.

## What became materially better

### Semantic kernel and authority

- `AcceptedCellEffect` is the common effect authority: exact request authorization, effect digest,
  pre-root, mode evidence, validated patch, and disclosure decision.
- `AcceptedCellEffectRequestBinding` closes selected lawful argument binding without adding a
  second authority token or interpreter.
- `CanonicalTransition` derives one typed post and dependent delta.
- `TypedCellHyperedge` and `MultiCellHyperedge` support schema-polymorphic, heterogeneous cells,
  exact per-leg authority/effects, retained nullifiers, aggregate resource laws, and one apex.
- Canonical credential authority state now carries issuance, strict attenuation, revocation, and
  epoch rotation through accepted cell effects.
- Resource/cost semantics and durable settlement are proof-native models rather than prose.

### Proof control and composition

- Lean computes exact SP 800-185 cSHAKE256 and byte framing.
- The Tower256 backend, Merkle schedule, LogUp controller, additive-FRI controller, Ext6 gate
  controller, note-spend controller, and BFV framing controller all accept opaque bytes/error only.
- One extensible same-coin failure ledger prevents unrelated proof systems from reusing a failure
  tag merely because a union bound is convenient.
- Retained history now stores its fold trace and derives its BCS claim/challenge chain instead of
  receiving a parallel caller-authored accumulator schedule.
- Additive accepted openings now use a raw carrier without universal `PositionBinding`: either all
  values pin to the literal committed words and ideal additive FRI holds, or an exact path-specific
  cSHAKE collision event is extracted.
- Intrinsic retained-history MCA/PCS extraction failure is charged to `historyPcs`, not laundered
  into commitment binding or ROM failure.

### Private computation

- Pure computation no longer carries a mandatory disclosure/release or a second authorization
  portal.
- Sealed computation has `PEmpty` release data; later disclosure must be a separate authorized
  effect.
- BFV retains every one of its 384 exact row equations and enters the common accepted-cell/history
  path without a receipt-side augmentation trick.
- Note spend reaches the common sealed computation core and has deterministic proof-control
  framing, while hiding/PoK/PCS/CR/ROM remain explicitly distinct premises.
- BFV opaque bytes currently produce only `ControlledReceipt`. Semantic `AdmittedReceipt` requires
  exact nonzero proof-codec, suite, and controller pins. The canonical BFV statement uses zero pins,
  and `statementOf_no_boundSuite` proves current semantic admission is impossible.

### Hyperdocuments and agents

- Content provenance uses an acyclic `OperationId`; final event identity may bind post-state
  without asking for a hash fixed point.
- Event log state is a separate append-only cell joined atomically with content publication.
- Concurrent siblings are admitted; generic causal admission no longer wrongly requires every
  parent to remain a frontier tip.
- Stable ranges distinguish live/tombstoned anchors, empty-run cuts, and explicit death policies.
- Transclusion references retain source object/history/semantic roots, representation/opening
  descriptors, version, mode, disclosure scope, and ceiling.
- History observations are indexed by an exact entry occurrence in an exact verified head; finality
  is indexed to that head/entry/root, and quote openings are post-state-only.
- Conservative merge retains every current parent and emits explicit provenance-bearing conflicts
  instead of erasing a writer. A selected base requires actual causal ancestry and an exact base
  realization; ambiguity is retained.
- Versioned user/agent interface negotiation returns bounded query/action surfaces, never ambient
  object authority or remote activation.
- The composed agent-operation slice now orders Promise→Notify→React before acceptance. The exact
  accepted effect first appears at Finalize; negotiation, receipt/history, invalidation, atomic
  logical content+event publication, replay rejection, and the conditional durable plan all derive
  from that same value.

## Things that nearly slipped through our fingers

These are more important than a generic TODO list because each one could support a convincing but
false claim.

1. **“Proved refinement kernel.”** There is no Rust semantics to refine. Lean proves its own
   semantic relation and checks candidate bytes. Keep using “Lean-owned admission” and “opaque
   fallible compute.”
2. **Binding assumed before binding was proved.** The old Merkle PCS carrier stored universal
   `PositionBinding`, so unequal openings had already vanished before the collision reduction.
   Raw carriers must retain the adversary's opening attempts.
3. **Intrinsic PCS failure misclassified as CR/ROM.** History extraction failure belongs to the
   history PCS/MCA event. Binding and ROM events must describe actual binding and transport failure.
4. **Circular lifecycle adapters.** The first Hyperdocument agent-operation draft accepted the
   effect before constructing Promise/Notify/React. The corrected shape begins with declaration and
   pre-state; acceptance first appears at Finalize.
5. **Caller-constructible proof suites.** A reflected `check_iff` record alone is not deployment
   authority. Suite/codec/controller identities must be exact, assigned, nonzero, and bound to the
   statement. Zero-pinned BFV is deliberately unadmittable.
6. **Logical atomicity mistaken for a database theorem.** Multi-cell and durable relations are
   semantic models. Physical transaction linearization, WAL recovery, replication, failover, and
   availability require `ImplementationRefinement` for a real handler.
7. **A history entry mistaken for accumulated history.** A valid entry alone is insufficient;
   observation needs exact membership/position in a verified head and finality indexed to that
   occurrence.
8. **Hyperdocument hash cycles.** Storing final post-root-derived event IDs inside the post-state
   would require a hash fixed point. Staged operation identity and a separate event cell avoid it.
9. **Tip-only causal admission.** Requiring all parents to be current frontier tips made a second
   offline/concurrent child of the same parent impossible.
10. **Claims based on stale OLean caches.** Exact archive builds exposed errors hidden locally.
    Targeted source compile and immutable remote evidence are load-bearing, not ceremony.
11. **Shared Lake symlink mutation.** The local `.lake/packages` tree points through Breadstuffs to
    shared checkouts. Lake reconciliation can delete or rewrite rebuildable shared cache state.
    Verification must use private copied/COW dependency trees.
12. **Contention presented as algorithmic cost.** A 291-second cSHAKE job in the umbrella was a
    scheduling/load observation; isolated exact builds were roughly 8–12 seconds. Matched profiling
    found a real import/RSS improvement, but there is no 291s-to-X speedup claim.
13. **A registry pin mistaken for a deployed verifier.** Clause 404 and BFV 901 are gated/reserved.
    Only clause 406 currently has a narrow positive byte-backed deployment path.
14. **A proof controller mistaken for security.** Transcript order, decoding, and reflected checks
    do not prove PCS soundness, collision resistance, ROM transport, proximity, knowledge, or
    hiding. Those events need concrete reductions and prices.
15. **A semantic nucleus mistaken for consumer subsumption.** No DeOS, Grains, DreggNet, agent,
    marketplace, authorization, or editor consumer has cut over. Replacement requires real D
    evidence and matched B evidence.

## What is still not materially started

“Not started” here means no honest production-strength path, even if a generic interface or
prototype exists.

- A real transactional durable handler over an actual database/filesystem/network representation.
- Consumer cutover for DeOS, agent-platform, Grains, DreggNet/cloud, Drex/FHEgg/Dark Bazaar, token
  authorization, or a Hyperdocument editor.
- Concrete end-to-end PCS/CR/ROM implementations and reductions for the deployed proof paths.
- Production confidentiality, malicious-MPC security, FHE security, proof-of-knowledge, or hiding.
- Assigned/deployed proof suite identities for note spend, BFV, Ext6, additive FRI, or history.
- A raw retained-history PCS carrier which keeps every adversarial opening pair and extracts either
  intrinsic history PCS failure or a concrete binding/ROM event on the same coin.
- General language lowering, broad effect interpretation, and physical side-effect completion.
- Production synchronization, replication, consensus/finality, search, indexing, garbage
  collection, quota/DoS policy, and availability for the medium.
- Production key custody/rotation ceremonies, schema migration, protocol upgrade governance, and
  compatibility policy across deployed artifacts.
- End-to-end proof latency/size/memory/tail benchmarks for real user/agent workflows.

## Consumer replacement gates

Do not call any row subsumed before deployment evidence exists.

| Consumer | First honest replacement slice | Still required |
|---|---|---|
| token authorization | one real issue/attenuate/revoke/use path over canonical authority cells | deployed storage handler, token codec/transport, cutover |
| DeOS / agent platform | one authenticated promise→notify→react→finalize→view/receipt workflow | scheduler/tool handler, persistence, UI/runtime adapter |
| Grains | one causal receipt chain plus succinct retained-history checkpoint | concrete history PCS/ROM, network/storage adapter |
| DreggNet/cloud | one costed multi-resource intent with durable external completion | transaction/WAL/replication refinement, provider adapter |
| Drex/FHEgg/Dark Bazaar | one sealed private trade/computation plus separate release | concrete proof suite, privacy/security, settlement adapter |
| Hypermedia clients | one link/annotation/edit with stable range, backlink, branch/merge, finality | persistent index/sync/editor, production history proofs |

## Precise proof/security residuals

### Additive Tower256

The representation gap is closed. `RawMerklePcs` has executable Merkle verification without
`PositionBinding`. False acceptance is constructively covered by additive proximity,
commitment-binding collision, or oracle transport on one ideal coin.

Still external:

- a probability bound for the fixed actual extracted-collision event;
- exact cSHAKE/common-coin transcript transport;
- production proof/container/domain codec identities; and
- end-to-end performance/security parameters.

### Retained history

The actual Fiat–Shamir failure predicate is fixed and intrinsic extraction failure maps to
`historyPcs`. The current bound history carrier cannot represent an unequal opening because it has
already consumed `PositionBinding`.

The missing object is a raw history BCS opening carrier over the executable commitment scheme.
For each coin and output round it must retain the literal adversarial `SrOutput`, exact semantic
round and query-coordinate attribution, a committed codeword whose commitment is that submitted
root, code membership, and the submitted value/path. The committed-word/root-preimage witness is
load-bearing: roots, columns, and accepted paths alone do not manufacture the honest second opening
needed by a collision reduction.

With that carrier, the fixed actual failure may split honestly: missing root/preimage attribution
is oracle transport failure; an unequal accepted submitted value yields the existing extracted
collision; and fully pinned openings feed erasure recovery and the intrinsic history PCS/MCA event.
Do not wrap the existing binding carrier and pretend it retained this evidence.

### Ext6

Deterministic transcript/algebra control and eight distinct failure classes are landed. Still
external: real gate PCS, base-subfield provenance, coherent proximity/final LDT, binding, ROM,
challenge-reduction bias, recursion, concrete IDs/codecs, and deployed security level.

### Note spend and BFV

Both statements are derived from the sole accepted sealed effect. Note spend has conditional proof
control; BFV has exact 384-row framing and a proof that zero-pinned statements cannot bind a suite.
Neither has a deployed succinct verifier, hiding, PoK, PCS, CR, or ROM theorem. BFV relation
acceptance does not imply FHE privacy or correctness of an opaque native implementation.

## Performance and build-system memory

- Generated Tower256 dot-product dispatch has matched byte identity and noise-scale overhead on
  hbox/persvati. This is not proof throughput.
- Sparse equality wins at low density; dense wins at high density; the middle band remains
  profile-dependent.
- cSHAKE Core/API/Conformance were split so ordinary consumers do not import conformance proofs,
  while `Compiler` still executes the NIST/FIPS vector checks. Exact hbox runs
  `E-20260810T010516-50252-hbox-85dee2aaf5cf-lake` and
  `E-20260810T010659-53862-hbox-85dee2aaf5cf-lake` are green and source-exact.
- Matched single-core hbox profiling reduced the ordinary API from 4.16–4.85 seconds and roughly
  4.08 GiB RSS to 2.19–2.44 seconds and roughly 2.60 GiB; the dependent backend went from
  4.01–4.26 to 2.61–2.74 seconds. Umbrella outliers were contention and must not be used as the
  baseline or advertised as a 291-second-to-X speedup.
- The local explicit-commit runner passed its macOS direct-shebang bootstrap and final isolated
  E2E. A clean `lake build Theory.CanonicalTransition` completed 2,953/2,953 with command, source,
  and dependency integrity all zero. A second fresh run intentionally mutated the archived
  `README.md` after a command exit of zero; the runner rejected it with exit 86, kept dependency
  integrity, and left the live README hash unchanged. Both runs used APFS clones with a complete
  cross-seed/run distinct-inode audit. The runner must never repair the current shared `.lake`
  topology by mutating or deleting user caches.
- GPUs exist physically on both large hosts but no usable ROCm path was available during this
  session. Current evidence is CPU-only.

## Quiescence worktree ownership

At the moment of the final quiescence pass, the only uncommitted repo path visible to the root agent
was this `QUIESCELOG.md`. The Hyperdocument operation lane finished cleanly at `83e59af`; the local
isolation lane finished at `7e571d6`; and the cSHAKE performance work finished at `85dee2a`.

Re-check with `git status --short`; this list is not permission to overwrite another lane. All
commits during wind-down must use exact pathsets. If a near-green lane cannot finish promptly, keep
the owned untracked file with a diagnostic note rather than sweeping it into an unrelated commit.

## Resume order

The next session should not begin with a random theorem from the longest TODO list. Resume in this
order unless new evidence changes the dependency graph:

1. **Establish a clean base.** Read this log, `README.md`, `GOAL.md`, `PROJECT.md`, and the two
   top-level subsumption audits. Check worktree ownership and exact commits. Use the isolated local
   runner or remote immutable runner; do not trust shared local OLeans.
2. **Finish the quiescent integration gate.** Import only completed raw-additive/history-event/BFV/
   Hyperdocument modules, run import-boundary checks, and perform one exact hbox umbrella replay.
   Run persvati only after its authenticated SSH/Tailscale path is restored.
3. **Build raw retained-history openings.** Reuse the additive raw Merkle carrier; do not wrap the
   already-binding `HistoryBcsOpenings` carrier.
4. **Instantiate one physical durable handler.** Pick one bounded consumer slice and prove its
   representation/step/WAL/retry refinement. This is higher leverage than another abstract receipt.
5. **Cut over one user/agent workflow.** The best candidate is a Hyperdocument link or annotation
   with promise/finalize, atomic content+event publication, invalidation, receipt/history, and
   durable handler.
6. **Close one real proof suite end-to-end.** Prefer the suite that serves the chosen consumer;
   supply exact IDs/codecs, PCS/CR/ROM/proximity/knowledge prices, and an authenticated artifact.
7. **Benchmark the admitted workflow.** Measure user-visible latency, proof size, memory, storage,
   network, and tails on both CPUs. Use Loom's kill criteria if the construction loses.
8. **Then broaden consumers.** Authorization, Grains/history, private market/FHE, and DreggNet/cloud
   should all compile into the same accepted-effect/durable-history spine rather than acquire new
   kernels.

## Things not to do on resume

- Do not add another turn mode, call tree, guard language, effect interpreter, receipt authority,
  or private-computation portal.
- Do not place an abstract verifier callback in authored data and call its proposition security.
- Do not add a `private` branch to `TurnTransition` or augment an already-committed receipt as the
  primary private-computation path.
- Do not import `Kernel` into candidate-independent `Theory` to gain a convenient theorem.
- Do not make history or quote finality a free `Bool = true` premise.
- Do not make a root a caller field when it can be derived from canonical bytes/state.
- Do not identify proof acceptance with hiding, executor privacy, access-pattern privacy, or release
  authorization.
- Do not describe a registry/catalog entry as deployed unless a real controller entry, byte path,
  artifact identity, and handler are joined.
- Do not use tests as Rust semantics or a benchmark as a correctness proof.
- Do not automatically sync generated/native/remote results into source.
- Do not share writable `.lake/build` or package metadata between concurrent runs.
- Do not accept “green locally” when a clean exact archive has not elaborated the target.

## Questions worth preserving

- Can one authenticated-column controller honestly serve lookup, sparse RAM, additive proximity,
  and retained history without erasing the different failure events?
- What is the simplest transparent, post-quantum, straight-line-knowledge-sound accumulator that
  retains arbitrary semantic receipt families?
- Where is the exact native/common representation boundary for FHE rings and MPC shares, and what
  observation theorem is actually required by the consumer?
- Can authenticated causal hypermedia become the native shared medium for users and agents—not a
  document store plus an agent sidecar?
- What are the real dense/sparse, checkpoint, proof-size, memory, and tail-latency crossovers?
- Can every false-accept route live in one reviewable same-coin ledger without pretending failures
  are independent?
- Which abstractions genuinely replace Breadstuffs/dregg2 functionality, and which merely describe
  a formal subset while runtime behavior remains elsewhere?
- What would falsify Loom as the right architecture? We should keep the answer executable and
  benchmarkable rather than rhetorical.

## Final strategic note

The session's most valuable progress was not raw line count. It was repeatedly moving authority
back to the exact object which should own it:

- state meaning into canonical typed cells;
- action authority into one complete request;
- computation acceptance into Lean controllers;
- private release into a separate authorized effect;
- cross-cell composition into a flat hyperedge;
- history meaning into retained typed entries/fold traces;
- failure pricing into one same-coin ledger;
- native work identity into authenticated generated artifacts; and
- deployment claims into explicit S/A/P/D/B gates.

The most important next milestone is therefore not “more Loom.” It is one user-visible workflow
which passes through all of those owners without a parallel runtime meaning. When that exists with
physical refinement, concrete proof security, and matched performance evidence, minidregg will
begin to subsume a real kernel rather than merely deserve to.
