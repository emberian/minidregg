# Objective manifest projection-collector evidence

Measured on 2026-10-08 with the repository's pinned Lean 4.30 toolchain.

## Lean 4.30 fault plant

The test module was temporarily changed to require Lean's built-in collector to contain the
structure name of this raw projection:

```lean
def projectionOnly : Expr := .proj `ProjectionOnlyStructure 0 (.bvar 0)

run_meta
  unless projectionOnly.getUsedConstants.contains `ProjectionOnlyStructure do
    throwError "RED plant: Expr.getUsedConstants omitted ProjectionOnlyStructure from raw Expr.proj"
```

Command:

```text
lake env lean Verify/ObjectiveManifestProjectionTest.lean
```

Result: exit 1 (RED).

```text
Verify/ObjectiveManifestProjectionTest.lean:11:0: error: RED plant: Expr.getUsedConstants omitted ProjectionOnlyStructure from raw Expr.proj
```

The plant was reverted. The checked-in module has a `#eval`-free elaboration-time check of the
fixed collector and fails its build if that edge is absent.

## Required builds

Build-service ticket `b429600704` ran:

```text
lake build Verify.ObjectiveManifest Verify.ObjectiveManifestProjectionTest
```

Both targets built successfully (exit 0). The build log is
`/home/ember/.cxo/builds/b429600704.log`.

## Full ObjectiveProofs-closure scanner measurement

The base source was `cfdaf64df8`; the tip was the corrected working source atop `7609a3a17b`.
Each ran in an independent `/tmp` snapshot with its own writable copy of `.lake`. The two real
scanner partitions used the same invocation as `scripts/check-objective-proofs.sh`:

```text
OBJECTIVE_MANIFEST_OUT=<out> lake env lean --root=scripts scripts/ObjectiveManifest.lean
OBJECTIVE_MANIFEST_OUT=<out> lake env lean --root=scripts scripts/ObjectiveManifestMathlib.lean
```

`/usr/bin/time -f '%e'` measured wall time around each invocation:

| source | Theory partition | Mathlib partition | sequential sum |
| --- | ---: | ---: | ---: |
| base `cfdaf64df8` | 2.60 s | 24.61 s | 27.21 s |
| corrected tip | 2.74 s | 28.53 s | 31.27 s |

Both runs scanned 2,191 Theory rows and 37,147 Mathlib-side rows. Both emitted 79,287 and
1,543,776 closure nodes, respectively.

For the edge comparison, each `C` record was keyed by its constant name and its dependency set was
the tab-separated fields after the fixed record columns. Across both partitions:

- base: 56,076 `C` records;
- corrected tip: 56,077 `C` records;
- 541 existing `C` records had changed dependency fields;
- 541 directed dependency edges were added and none removed;
- the added edge targets were `PProd` and `WellFoundedRelation`;
- the new edge to `WellFoundedRelation` brought that one additional constant into the closure.

