# Authored presentation Surfaces

A Surface is presentation data that an authored program returns and a renderer
displays: finite nodes, observed slots and native-action intents. It is not
an evaluator and grants no permission to read or mutate the world. (For the
Objective Bend source language itself see
[OBJECTIVE-BEND-FRONTEND.md](OBJECTIVE-BEND-FRONTEND.md).)

## State

- `Compiler/BendWorldSurface.lean` owns the canonical framed encoding of
  `Surface`, `Node` and `Intent`.
- `native/resource-client/src/world_surface.rs` consumes that decoder's JSON
  projection and checks structure, origin equality, admitted observation
  indices and every intent field; `native/resource-client/src/web/surface.rs`
  renders it with escaped prose and bounded traversal.
- The shared source declarations are `world/Workshop/WorldSurface.bend`, a
  Gen-1 Bend file. No Objective Bend (`.obend`) program declares or returns a
  Surface, and the Objective elaborator has no Surface output lowering. An
  Objective producer needs the Surface types written as `.obend` records and
  sums (sums are available: `sum` declarations, `S.l(e)` and `match`) and a decoder from the checked
  Core4 result to the canonical `Surface`.
- The public Surface route is not registered.

## Presentation contract

A Surface binds an immutable source artifact and logical export name. Nodes are
finite and address earlier child nodes. A root selects the reachable graph;
rendering bounds depth, expansion and output size. Separate mounts receive
caller-owned identifiers so repeated views keep separate anchors.

| Tag | Meaning | Data source |
| --- | --- | --- |
| 0 | Authored prose | Exact source return label |
| 1 | Observed value | Individually admitted observation slot |
| 2 | Document or object mount | Individually admitted observation slot |
| 3 | Native action | Exact intent binding and independent preparation |
| 4 | Group | Earlier child node indices |

The source result cannot supply observation bodies, enabled flags, arbitrary
HTML, script URLs or discovery queries. Observed slots keep exact source
revisions and disclosed, locked, refused or unavailable states. Installing a
view creates no rights.

An Intent binds `artifact`, logical `exportName`, immutable `program`,
`instance`, `expectedRoot` and exact `arguments`. The renderer offers a native
review route only through a separately supplied custody map for a matching
prepared intent. Rendering performs no read, preparation, approval or
submission; native review and admission reread current authority and roots.

## What a source-to-Surface route still needs

1. Surface record and sum declarations in `.obend`, replacing the Gen-1
   `WorldSurface.bend`.
2. A decoder from the checked Core4 result (deep Data) to the canonical
   `Surface`: byte lists bounded to bytes with refusal (no wrapping), exact
   UTF-8 and NUL-free strings, canonical digests, bounded indices, backwards
   children.
3. Origin binding: the returned artifact/export label must equal the
   independently accepted execution attribution.
4. Native preparation and custody adapters for intents; the Studio editor,
   diagnostics and governed publication joins.

The native tests cover forged observation/enabled fields, exact source and
action bindings, unknown and cyclic nodes, markup escaping, traversal bounds
and independent mount anchors. They are tests of the Rust consumer, not of any
source producer.
