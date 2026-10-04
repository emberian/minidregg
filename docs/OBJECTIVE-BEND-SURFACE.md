# Authored Objective Bend surfaces

This is an additive source interface and generic presentation consumer. The
native/browser implementation compiles and its five scoped tests pass. The
canonical Lean codec and refinement proofs await their scoped check. The public
Surface route is intentionally not registered yet: accepted core return lowering,
selected-provider attribution and actual native preparation must join first.

`Compiler/BendWorldSurface.lean` owns canonical framed encoding of `Surface`,
`Node` and `Intent`. They are presentation data, not an evaluator or permission
to read or mutate the world. The source-side declarations exist only as
upstream-Bend source (`world/Workshop/WorldSurface.bend`, checked through the
retiring BendTT path); an Objective Bend (`.obend`) declaration of Surface does
not exist yet.

## Presentation contract

A Surface binds an immutable source artifact and logical export name. Nodes are
finite and address earlier child nodes. A root selects the reachable graph;
rendering bounds depth, expansion and output size. Separate mounts receive
caller-owned identifiers so repeated views retain separate internal anchors.

| Tag | Meaning | Data source |
| --- | --- | --- |
| 0 | Authored prose | Exact source return label |
| 1 | Observed value | Individually admitted observation slot |
| 2 | Document or object mount | Individually admitted observation slot |
| 3 | Native action | Exact intent binding and independent preparation |
| 4 | Group | Earlier child node indices |

The source result cannot supply observation bodies, enabled flags, arbitrary
HTML, script URLs or discovery queries. Native observed slots preserve exact
source revisions and disclosed, locked, refused or unavailable states. Installing
a view creates no rights.

An Intent binds `artifact`, logical `exportName`, immutable `program`, `instance`,
`expectedRoot` and exact `arguments`. The renderer offers a native review route
only through a separately supplied custody map for a matching prepared intent.
Rendering performs no read, preparation, approval or submission. Native review
and admission reread current authority and exact roots.

## Actual source origin and output lowering

The returned artifact/export label must match independently accepted execution
attribution. Logical provision selectors and source definitions differ from
elaborated core field names; preserve both. Objective Bend has no linker: a
composed specification elaborates to one `fix` over a chain of `mix`, and nothing
records which specification supplied a method. Provider attribution therefore has
no source today. An arbitrary transcript or annotation does not establish it.
(The Gen-1 linker that once supplied this mapping was deleted on 2026-10-04.)

The required core-return decoder must derive the typed Surface from the actual
checked result. Source byte lists contain Nats: reject out-of-range bytes rather
than wrapping, require exact UTF-8 and NUL-free string fields, canonical digest
representation, bounded indices and backwards children. Bind the exact output
codec and effect ABI into the source artifact profile after codec checks.

`world_surface.rs` consumes the canonical decoder's JSON projection. It checks
structure, origin equality, admitted observation indices and every intent field.
`web/surface.rs` renders that projected data with escaped prose/data and bounded
graph traversal. Neither module constitutes a source compiler or kernel
authorization theorem.

## Source editing and governed publication

The next Studio consumer should join the existing authorized document editor
with the actual source package, import closure, checked core term and selected
entry. Preview presents real diagnostics, results and source/core mappings. Publication uses the ordinary governed content receiver
and exact expected root. Instantiate/evolve keeps old pins and current inherited
law; stale drafts remain available for an explicit new-base edit.

Source-interface origin is separate from data provenance. An app-export receipt
can describe a separately authorized document's content origin; it is neither a
Bend source export nor action authority. Resident outcomes similarly use signed
room/document projections and exact request identities, not controller journals.

## Qualification boundaries

The native tests cover forged observation/enabled fields, exact source and action
bindings, unknown/cyclic nodes, markup escaping, traversal bounds and independent
mount anchors. Release compilation passes. The upstream-Bend declarations had
sealed parsing and emission evidence on the retiring BendTT path; that evidence
does not carry over to Objective Bend.

Still required: scoped Lean compilation, accepted core-output lowering, actual
provider/source attribution, native preparation and custody adapters, source
editor/diagnostics/publication joins, and end-to-end authored browser/document
mount receiving. Fixed inspectors remain useful foundations, not completion of
Objective Bend.
