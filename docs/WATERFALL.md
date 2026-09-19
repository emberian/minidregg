# Waterfall for proof discovery

The 2026-09-19 minicycle checked [Waterfall](https://samth.github.io/waterfall/)
against three actual Mini obligations. All three searches succeeded. Their
ordinary tactic scripts were then checked in fresh Lean processes **without a
Waterfall import**, with exact axiom guards. Only the improved inverse-tag proof
was integrated; Mini has no new dependency or toolchain change.

## Pinned setup

- Upstream: <https://github.com/samth/waterfall>
- Commit: `4acadf6e12c06caac50b4e99e0753711b7426354` (version 0.1.0, Apache-2.0).
- Upstream targets Lean 4.33.1; its official page also reports testing 4.30.0.
- This study compiled its complete public import closure, unchanged, using
  Mini's existing **Lean 4.30.0**. No external package dependencies were needed.
- Eight modules, in order: `waterfall/Protocol`, `waterfall/Choices`,
  `waterfall/Core`, `waterfall/Committed`, `waterfall/Parallel`,
  `waterfall/Suggestions`, `waterfall/Tactic`, `waterfall`.

Clone and pin upstream in scratch, then compile those modules serially using
the existing 4.30.0 executable, `LEAN_NUM_THREADS=1`, and the clone's
`.lake/build/lib/lean` as `LEAN_PATH` and output directory. Do not invoke the
clone's default 4.33.1 toolchain against Mini's 4.30.0 oleans. For discovery,
prepend the scratch library to the `LEAN_PATH` returned by `lake env printenv
LEAN_PATH` in Mini. Respect the current fleet's compiler-seat limit.

The study used `waterfall? (cpus := 1) (attemptHeartbeats := 2000000)
(report := true)`, effort 120 for inverse-tag/length and 180 for append, with
enclosing `maxHeartbeats := 150000`. Supply imported recursive definitions in
brackets; automatic discovery of local definitions is not enough for these
imported Mini functions.

## Checked results

| General obligation | Attempts | Search raw heartbeats | Replayed axioms |
| --- | ---: | ---: | --- |
| `decodeVerb kind tag = some verb → verbTag verb = tag` | 92 | 34,133,737 | `propext, Classical.choice, Quot.sound` |
| `(bytesSlots stem offset bytes).length = bytes.length` | 32 | 1,623,879 | `propext` |
| `bytesSlots` distributes over append with the suffix offset advanced by prefix length | 47 | 3,519,159 | `propext, Classical.choice, Quot.sound` |

These are general quantified proofs, not closed examples. The tag search
imported only `Theory.AuthorizationDeclaration`, excluding the Compiler module
containing the already-proved private target. The recursive searches imported
the actual `Compiler.ResourceAuthorityProjection.bytesSlots`; neither target
lemma was already present there.

The inverse-tag suggestion used `fun_cases decodeVerb kind tag`, followed by
grind on each branch and simplification on the impossible branch. Both the
literal suggestion and this normalized script were checked separately:

```lean
fun_cases decodeVerb kind tag <;>
  grind +lax [decodeVerb, Minidregg.Theory.AuthorizationDeclaration.verbTag]
```

This now proves the unchanged private `verbTag_of_decoded` theorem in
`Compiler/TypedAuthorizationRequestCodec.lean`. It replaces manually counted
successor cases, which had become stale when the verb set grew. The actual
module compiled to olean/ilean/C; its consumer
`encodeRequest_of_decodeRequest` retains the standard three-axiom footprint.

The two byte-slot proofs remain study artifacts rather than unused production
API. These are the replayed ordinary scripts, with original theorem parameters
`stem : String`, `offset : Nat`, and byte lists of type `List UInt8`:

```lean
-- (bytesSlots stem offset bytes).length = bytes.length
expose_names
fun_induction bytesSlots stem offset bytes
expose_names
focus (first | assumption | rfl | contradiction)
expose_names
focus ((simp_all (config := { maxSteps := 100000, maxDischargeDepth := 2 })
  [bytesSlots]; done))
```

```lean
-- bytesSlots stem offset (xs ++ ys) =
--   bytesSlots stem offset xs ++ bytesSlots stem (offset + xs.length) ys
expose_names
(revert ys; fun_induction bytesSlots stem offset xs)
expose_names
focus ((simp_all (config := { maxSteps := 100000, maxDischargeDepth := 2 })
  [bytesSlots]; done))
expose_names
grind +lax [bytesSlots]
```

The literal generated scripts contain harmless redundant tactics/simp
arguments and produce linter warnings. Simplify them only with another check.

## Discovery and independent verification

1. State an actual general obligation using the production definition. Avoid
   importing the theorem being rediscovered. Keep study files in scratch.
2. Run bounded, single-worker `waterfall?` with relevant imported definitions
   supplied explicitly. Increase effort only for a concrete reason.
3. Copy the suggested ordinary commands into a new file without `import
   waterfall`. Recheck in a fresh Lean process. If shortening the script,
   recheck the shortened version too.
4. Pin `#print axioms` with `#guard_msgs`. Do not permit `sorryAx` or treat a
   compiled decision axiom as a kernel-only proof. Recheck the actual consumer
   after integration, maintaining the Theory import boundary.

Waterfall's suggestion frontend reparses the displayed text and elaborates it
from the original checkpoint with recovery disabled. Its root checker rejects
unassigned roots, unresolved metavariables, and direct sorry terms. That is
useful validation, but does not replace transitive axiom accounting. This study
did not run the upstream full test suite or benchmark Mini broadly.

Local evidence for this run is under
`/tmp/minidregg-cycle-20260919/waterfall-study/`: pinned clone, build/search
scripts, `TagReplayExact.lean`, `TagReplay.lean`, `RecursiveReplay.lean`, and
per-stage logs. The proof scripts and procedure above are the durable record;
the temporary directory need not survive.
