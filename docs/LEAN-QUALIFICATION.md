# Lean compilation and qualification

Source-first publication keeps authored work on main. A declared target, an owner report, successful elaboration, a general semantic theorem, and a native receiving result are different facts. The source inventory records hashes and owner reports; it does not manufacture a compiler result.

Use the pinned toolchain and dependencies in `lean-toolchain` and `lake-manifest.json`. On a designated build host, use its resource guardian and one coherent warm namespace. Lake may build missing dependencies: inspect the import closure before a scoped check.

| Target | Purpose | Limits |
| --- | --- | --- |
| `lake build Minidregg` | Stable per-directory roots and previously orphaned carry/recovery gates | Does not claim the authored research tree compiled |
| `lake build ObjectiveProofs` | The Objective Bend Core4 metatheory over the default-build definitions | Gated separately from `Minidregg` |
| `lake build ResearchWip` | Opt-in research library, generated: every library module no other target reaches (it includes the generic arithmetic/IR2 stack and `Assurance.BendArithmeticQualification`) | Not part of the default gate; may fail |
| `lake build SimplexQualification` | Executable causal/history/emission closure, global engine safety, general prepared-jump safety and inhabited/hostile witnesses | Consensus closure requires `n = 3f+1`, authenticated `AllowedInput`, actual `Reachable`, and the fault bound; native signed participant receiving is a separate consumer |
| `python3 scripts/lean-build-surfaces.py research` | Remaining authored library modules and standalone program roots | Explicit opt-in; may fail and does not gate ordinary source publication |

`python3 scripts/lean-build-surfaces.py generate` writes the emitted targets (`SimplexQualification.lean`, `ResearchWip.lean`) and the surface report `build-logs/lean-build-surfaces.json` (a build output, untracked). Its `check` command regenerates into a scratch directory and rejects an emitted target that git does not track or that differs from what the generator writes now. `scripts/check-build-closure.sh` checks declared coverage; compilation is performed by the actual targets above. Research compilation is excluded from the normal gate runner and reported as opt-in. No successful structural scan substitutes for a compiler result.

The four formerly orphaned carry/recovery gate modules are imported by `Minidregg`. `Verify.JointDecisionRecovery` now uses `#assert_axioms`, so nonstandard axioms fail elaboration; bare printing was diagnostic only. Axiom checks constrain trust, not theorem strength. The controller fixture assertions use explicit compiled checks. General statements and their assumptions must still be reviewed.

Import tiers are checked by `scripts/check-import-boundary.sh` (the `import-tiers` gate) over every tracked `.lean` file. Its table carries one deliberate relaxation: commit `76757030` (2026-10-03) let `Theory` and `Kernel` import `Lean`, `Std` and `Init` in addition to Mathlib and the tree's own libraries. The toolchain is not candidate code, but the check is weaker than the 2026-10-01 table it replaced (the metatheory may now import the elaborator), and the script header names it as such. Narrowing it is an edit to that table. On 2026-10-04 the `Theory` row was narrowed back to `Mathlib`, `Lean` and `Theory`: the deleted upstream-Bend kernel was its only `Std`/`Init` importer. On 2026-10-05 the `Host` row gained `Std` (first importer `Host/FnArchivePublisher`, `Std.Internal.Async.TCP`); it widens no closure, since `import Lean` already reaches that module through `Lean.Elab.Idbg`.

The current evaluator registry remains Nock-only. Registering an Objective Bend evaluator requires the independent specification, soundness, completeness, deterministic/crash/exhaustion laws, stable metering and byte-entry relations in `Compiler/Evaluator.lean`; a reference adapter does not discharge them merely by returning a proof-carrying trace.

The dated intake ledger records published source status. Aggregate targets added by this change have not yet received an aggregate compiler PASS. Qualified component snapshots and native receipts remain separate evidence. The modern source tree is not the historical service executable.

To emit the actual imported theorem statements and their axiom footprints, run
`lake env lean scripts/report-simplex-qualification.lean` after building
`SimplexQualification` and `Compiler.QualificationReport` (the emitter's separate
import, not part of the qualification target's closure). Each `QUALIFICATION_CLAIM` JSON row comes from the elaborated
environment. The emitter labels compiler trust and does not infer premise
inhabitation or hostile witnesses from a name, an axiom scan, or a case count.

`Kernel.GenericSimplexJumpSafety` proves maximum-prepared selection and the actual
`enterView` frame/clock contract. `progressOuter_split` pins its internal jump
boundary to `ordinaryOuter c s`, the executable ordinary prefix, and proves
`progressOuter c s = jumpStep c (ordinaryOuter c s)`. The jump-safety guard is
evaluated on that pinned pre-jump state, never an existentially chosen outcome.
`jump_guard_inhabited` derives origin from the reachable admitted schedule and
checks that the actual first delivery-pass prefix has current view 1 and maximum
prepared view 2, then applies the general jump-safety theorem at that boundary.
Its `reachable_step_safety` derives
history/vote provenance and commit/delivery prefix compatibility from the actual
`Reachable.next` transition. It does not assume `AuditRefinement`. The admitted
`jumpSchedule` and `jump_nonvacuous` witness an honest laggard moving from view 1
to view 3 when its final authenticated delivery completes a view-2 vote quorum;
these finite witnesses inhabit the theorem premises, not replace the proof.

The selection/frame lemmas are parameter-independent, but the reachable
consensus theorem is **only** for `n = 3f+1`. In particular, committees of size
5, 6 or 8 cannot satisfy that equation for any natural fault bound, and
`Config.wellFormed` rejects them. This qualification does not prove their safety,
native integer-overflow behavior, cryptographic authentication, liveness or
mixed-version compatibility. `Verify.GenericSimplexJumpControls` contains finite
field-level selection/successor/deadline/lock/quorum controls for source mutation
checks; full-state finite equality is not the safety argument.

On a Fabric snapshot, run `scripts/build-mini-kernels.sh`, then `lake build SimplexQualification
Verify.GenericSimplexJumpControls Compiler.QualificationReport`, followed by `python3 -I
scripts/check-simplex-jump.py claims` to verify the nonempty elaborated theorem
statements and standard-only axiom footprints. `python3 -I
scripts/check-simplex-jump.py mutate` compiles nine executable mutants, requires
the named field-level control to fail with its axiom pin, restores the source,
and checks the restored controls. Missing-jump and jump-to-j mutants must also
fail `progressOuter_split` itself: the checker compiles the artifact's exact
prefix/jump/split declarations in isolation, with a passing baseline and restored
control, so no downstream proof failure can masquerade as this regression check.
Removing the jump is the must-fail-before control; min-selection, unprepared
hints, wrong successor/deadline, invented
disables, lost locks, duplicate votes and a reduced READY threshold are separate
mutants. These commands are not to be run on the development hub.

For source binding, pass a DATA-only `git archive` of the ClockDAG tip's
`clockdag-simplex-oracle/Kernel/GenericSimplex.lean` and
`crates/mesh-simplex/src/lib.rs` through Fabric `--input`. The checker's `bind`
command takes explicit `--clockdag-tip`, `--native-sha256`, and
`--oracle-sha256` pins. It checks the archive's commit, both complete file hashes,
and normalized whole-kernel equality allowing exactly the documented
newest-versus-oldest checked-offer policy and the exact upstream module-exposure
header (legacy `import Std` versus the enumerated `module`/`import all` header).
No executable namespace tokens or other imports are erased. Run `python3 -I -m
unittest discover -s scripts -p test_simplex_jump.py` to check that changed imports
and missing/wrong jumps remain visible to the binding, the adapter rejects extra
imports in either input, and injected compiler/mutation failures restore the
local source.

`--kernel-check` validates the raw pinned files first, then substitutes **only**
the enumerated upstream module-exposure header in a temporary C5 oracle copy.
It preserves the oracle namespace body byte-for-byte and checks normalized
whole-kernel equality; no arbitrary import removal is permitted. The real
adapter guard must refuse an extra import beyond that header. The checker
compiles the actual `SimplexQualification`, control and claim-emitter closure
against this **header-adapted oracle**, verifies its 16 nonempty standard-axiom
claims, and runs all nine compiled mutants plus both missing/wrong-jump split
assertions on that same adapted source. Passing baseline/restored controls and
distinct baseline/mutant hashes identify the actual tested representation.
Finally it restores the local source and rebuilds its proof closure even if an
oracle build or mutation check fails.

This is **header-adapted oracle compilation**, not compilation of the raw oracle
file. The original qualification on `1d693d1098ffe9a766e350e9a30dbad3f4de5cad`
compiled the exact legacy C5 file before the upstream module migration; that
historical result does not qualify a changed successor tree. Neither check
executes or extracts the archive or pretends source binding is a formal Rust/Lean
refinement; a directed native Lean/Rust differential receipt at the pinned C5
tip remains separate evidence.
