# Authored Objective Bend surfaces

This is an additive source interface and generic presentation consumer. The
native/browser implementation compiles and its five scoped tests pass. The
canonical Lean codec and refinement proofs await their scoped check. The public
Surface route is intentionally not registered yet: accepted core return lowering,
selected-provider attribution and actual native preparation must join first.

`Compiler/BendWorldSurface.lean` owns canonical framed encoding of `Surface`,
`Node` and `Intent`. The shared Bend source declarations are in
`world/Workshop/WorldSurface.bend`. They are presentation data, not an
evaluator or permission to read or mutate the world.

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
emitted core entry names; preserve both. The Objective Bend linker supplies the
actual selected provider and resolved self/super mapping. An arbitrary transcript
or annotation does not establish this mapping.

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
with the actual source Package, import closure, checked Book and selected entry.
Preview presents real diagnostics, open requirements, selected providers and
source/core mappings. Publication uses the ordinary governed content receiver
and exact expected root. Instantiate/evolve keeps old pins and current inherited
law; stale drafts remain available for an explicit new-base edit.

Source-interface origin is separate from data provenance. An app-export receipt
can describe a separately authorized document's content origin; it is neither a
Bend source export nor action authority. Resident outcomes similarly use signed
room/document projections and exact request identities, not controller journals.

## Qualification boundaries

The native tests cover forged observation/enabled fields, exact source and action
bindings, unknown/cyclic nodes, markup escaping, traversal bounds and independent
mount anchors. Release compilation passes. Shared source declarations have
upstream sealed parsing and emission evidence from their authored consumer.

Still required: scoped Lean compilation, accepted core-output lowering, actual
provider/source attribution, native preparation and custody adapters, source
editor/diagnostics/publication joins, and end-to-end authored browser/document
mount receiving. Fixed inspectors remain useful foundations, not completion of
Objective Bend.
