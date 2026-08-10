# D-0005 — Hyperdocuments as a semantic/history family

- Status: accepted; semantic/admission core landed, deployment and consumer cutover open
- Date: 2026-08-09
- Replaces: the parallel Breadstuffs document heaps, patch histories, transclusion demos, and UI-owned provenance stores

## Decision

Hypermedia is a first-class instance of the Lean-owned semantic/effect/history machine. A
hyperdocument is not an opaque byte blob placed under a root and it is not a Rust `DocGraph` whose
meaning is reconstructed by each consumer. Its canonical schema names typed content, stable ranges,
fields, conflicts, marks, annotations, links, transclusions, authority-bearing resources, causal
versions, and derived view/index state.

Every authoring operation is a typed accepted cell effect. An operation binds its canonical bytes,
principal and authority path, exact causal parents and pre-root, exact typed patch and footprint,
post-root, and semantic-history entry. A gesture spanning several independently rooted cells is a
flat multi-incidence hyperedge, not a Mina call forest. A document stored as one sparse container may
use an internal typed hyperedge; cross-cell composition must use an actual multi-pre/multi-post
carrier rather than pretending several roots are one state.

Rust may store, render, index, diff, search, and execute bounded candidate kernels. Lean owns IDs'
canonical preimages, codecs, operation validity, causal and conflict semantics, authority, transcript
and receipt meaning, and acceptance. A runtime-created object has no semantic authority merely
because a later field stores its digest.

## Landed boundary

- `Hyperdocument` defines typed content/field/conflict/link/transclusion/mark/annotation/event
  objects, sparse namespaces, canonical cells, and domain-separated identities.
- First-order create/edit/link/transclude/mark/annotate operations enter ordinary
  `AcceptedCellEffect`; family-generic request binding can pin their selected argument bytes.
- Content and causal-event cells publish as one accepted two-incidence `MultiCellHyperedge`.
- Exact-head history admission indexes the precise entry, occurrence, derived receipt root, and a
  supported finite injective post layout; concrete PCS/CR/ROM remains explicit.
- Concurrent merge opens every current parent content root. One field source writes; two or more
  sources always produce a provenance-bearing `ConflictRecord`. Marks and annotations are retained.
- Proof-relevant ancestry distinguishes a selected base, ambiguous bases, and no base. A selected
  base is opened at its exact realized root and feeds the ordinary accepted merge publication
  inputs; ambiguous or unavailable bases remain explicitly absent. It does not assert an arbitrary
  unique least common ancestor.
- `HyperdocumentInterface` supplies versioned first-order content/mutation/history interface IDs,
  lawful argument binding, exact request-indexed authority, pure direct-read projections, and
  history-query declarations. It supplies no callback, remote activation, accepted effect,
  host-index completeness, finality, or persistence.

This is **S/A**, not physical persistence, finality, a full CRDT policy, or a migrated editor.

## Required semantics

- Domain-separated canonical preimages for document, content/run, event, mark, annotation, link,
  transclusion, branch, and checkpoint identities. Hash binding remains an explicit cryptographic
  premise; finite hashes are not injective by definition.
- Typed sparse namespaces with stable semantic keys. Every semantically effective value, including
  embed repins and conflict resolutions, participates in the canonical root and exact footprint.
- A causal version DAG with explicit parent frontier, duplicate and missing-parent rejection,
  checkpoint/suffix replay equivalence, and no retroactive reinterpretation under current policy.
- Conflict values that retain every alternative and its provenance. Lossy text or DOM projections
  are observer views and cannot be edited back as authoritative state without a conflict-aware effect.
- Stable ranges with explicit endpoint-death and bias policies; marks and annotations are canonical
  state/history objects rather than adjacent in-memory overlays.
- One durable transclusion reference binding source domain/object/history entry, semantic root,
  range or value opening, snapshot/live policy, disclosure, and capability ceiling. Chains retain
  every adjacent weld.
- Forward link events and authenticated reverse indexes with a stated completeness domain. A
  best-effort search result is never mislabeled as a complete backlink fact.
- Observer-indexed reactive views and agent affordances derived from canonical dependencies and
  accepted deltas. Humans and agents use the same rights and effect grammar.

## Patch and merge claim ceiling

The Breadstuffs `DocMerge` model proves a useful semilattice join and therefore a pushout in the thin
category induced by its inclusion order. Preserve that algebra where its invariants apply.

Breadstuffs' patch-list category is genuinely non-thin, but its custom `IsoP` is state round-trip,
not `CategoryTheory.Iso`, and its custom "pushout up to iso" is not a colimit in that patch category.
Minidregg will either:

1. prove exact residual/commutation and join laws over the canonical operation semantics; or
2. define a justified contextual-equivalence quotient, prove congruence under composition and
   compatibility with authority/history, and only then state categorical results.

Names such as isomorphism, pushout, I-confluence, binding, and refinement are reserved for their exact
proved definitions. Rust tests remain executable evidence, not semantics or refinement theorems.

The current merge deliberately takes the conservative option before a richer resolution algebra:
it retains exact parent realizations and makes every multi-source field conflict explicit. A
common-base identifier is absent unless ancestry proves it, and base selection may be ambiguous.
When ancestry selects a base, exact base realization/root evidence is retained through the
accepted multi-cell publication. This does not prove physical database atomicity or finality.

## Hard invariants and non-claims

- Authorization precedes mutation. Rejection or blockage exposes no logical post-state.
- Historical authority is evaluated at the event's committed epoch. Revocation governs future
  admission and does not erase previously valid history.
- Branch settlement consults current authority and appends one proof-relevant settlement event; it
  never resolves conflicts by dropping alternatives from a rendering.
- Consensus/finality may order semantic receipts but does not define document merge semantics.
- Durable CAS, multi-database atomicity, scheduler fairness, storage availability, hash binding,
  PCS/ROM soundness, and renderer/Rust representation correspondence remain explicit boundaries.
- The architecture does not claim the current Breadstuffs runtime refines these semantics. There is
  no Rust semantics to refine. Migration requires generated contracts, checked adapters, and trace
  evidence, followed by deletion of handwritten semantic mirrors.

## Cutover evidence

The old kernel is not replaced for a document consumer until:

1. every accepted edit opens to its exact canonical event, authority, pre/post state, footprint, and
   accumulated history entry;
2. conflicts, ranges, annotations, links, and transclusions survive replay, rendering, merge, and
   settlement without silent erasure or retargeting;
3. backlinks and query answers disclose their completeness domain and carry openings or an explicit
   best-effort label;
4. offline exchange handles missing parents, checkpoints, replay, current-authority settlement, and
   rollback/replay resistance;
5. production codecs and optimized kernels are selected by Lean-emitted descriptors and their exact
   candidate outputs are checked before acceptance; and
6. workload evidence shows sparse incremental update/proof costs rather than whole-history replay,
   reseal, and serialization per edit.

## Why this belongs in Loom

A hypermedia edit simultaneously touches content, causal history, authority, links, views, indexes,
and sometimes private computation. A quote crosses object identity, history, finality, disclosure,
and representation. A merge joins causal content while consulting present authority. These joints
cannot safely be recreated by convention in each renderer, editor, agent tool, and storage service.

Loom is the assurance fabric that makes the specialized execution and proof dialects refer to the
same semantic event. It is not a universal field or universal AIR.

## Compound-document design analogy, not lineage

DCOM/OLE and earlier compound-document systems correctly emphasized active embedding/linking,
interface negotiation, marshaling, remote activation/events, aggregation, and distributed commit.
minidregg does not claim direct lineage or one-to-one replacement. It contrasts their ambient
pointers, identity/location/configuration, and hidden mutation with explicit evidence:

- monikers → typed content-addressed references;
- structured storage → canonical sparse authenticated cells;
- embed/link → authenticated transclusion plus backlink/history evidence;
- `QueryInterface` → an explicit typed effect family/manifest clause, not runtime object authority;
- proxy/stub marshaling → lawful codecs and generated bytes/error dispatch;
- aggregation → a flat typed multi-cell hyperedge;
- connection points → verified reactive lifecycle; and
- distributed commit → fail-closed multi-root/nullifier/budget/history journal semantics.

The analogy preserves the active-compound-medium ambition while changing where identity,
authority, transition meaning, and history come from.

## Source audit

- `/Users/ember/dev/HYPERDREGGMEDIA_MINIDREGG_SUBSUMPTION_AUDIT_2026-08-09.md`
- `/Users/ember/dev/BREADSTUFFS_MINIDREGG_SUBSUMPTION_AUDIT_2026-08-09.md`
- Breadstuffs audit snapshot: `89c254c251d0168c7155438cc8cabeed4d7786c2`
