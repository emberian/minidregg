# Cold audit: retained composed-law admission

The matched source 6075eff2 JLI run2 retained two different accepted histories. Its first normal cold audit passed 19 records; after successful law exports/pins/updates, a second normal cold audit passed 30 records. These are full signed-ingress re-admission audits, not cached opens. No old c29 or duplicate audit was run for this investigation.

Final cumulative phase totals (earlier progress snapshots are not added):

| Measured phase | 5-record smoke | 19-record JLI | 30-record post-law JLI |
|---|---:|---:|---:|
| All measured phases | 1.1533s | 17.5913s | 31.5326s |
| Birth admission / event-v2 | 0.1927s (1) | 13.9549s (6) | 18.0552s (6) |
| Policy installation | absent | absent | 4.2910s (9) |
| Invocation / event-v3 | 0.1013s (1) | 1.6998s (10) | 2.5820s (11) |
| Advance | 0.1829s | 0.8740s | 3.9350s |
| Post-validation | 0.0377s | 0.3726s | 0.7281s |

The measured totals omit some bookkeeping and are not wall time. The six births dominate the richer runs (79.3% and 57.3%). Both record 16 progress snapshots already include all six births. Later law records therefore cannot explain a change in those original-prefix birth contexts; the timings are not controlled A/B measurements. Neither the five-record smoke nor this table establishes252- or1000-record scaling.

Evidence: `/home/ember/build/codex-world/core-smoke-6075eff2/cold-audit.err` and `/home/ember/build/codex-world/jli-core-6075eff2-run2/{audit.err,audit-after-law.err}` on persvati. Matching source/binaries are recorded in `bin-core-6075eff2/manifest.json`.

Source and generated C both show birth `Pending.admitBranch` calling `branchReadGuards` (loads authenticated graph and guards), then `Config.resolve?` (loads head/graph for witness), then ordinary `admit` → `Config.verifies` (loads the same head/graph again). The DRC authorization path similarly resolves a law before ordinary admission. No timing within that family yet apportions its total among decoding, projection, signatures, source resolution, lowering and other preparation.

The focused repair introduces `PreparedLaw.verifies` with exact Boolean equality to `Config.verifies` for any supplied witness, using the existing `headExact` and `graphExact` equations. `PreparedLaw.admit` and ordinary `admit` share one internal gate. A thunk preserves address, membership, then policy evaluation order. The complete Option Authorized equality retains failures, evidence and witness values, not merely success equivalence. Birth and DRC consumers pass their existing resolved law. Physical source guards, dependency checks, source loading for that retained law, signatures, compiler compatibility, witness binding, range/cast checks and effective-law evaluation remain mandatory.

Scoped shared-module compilation passes; both exactness theorems have guarded axiom sets containing only propext, Classical.choice and Quot.sound. Generated C for ordinary Config.verifies calls loadPolicy and PolicyComponentResolution.loadTarget; PreparedLaw.verifies calls neither, retaining the same step binding, compiler compatibility, closure digest and ResolvedLawCompilation.checks. PreparedLaw.admit dispatches through the shared gate with the retained verifier thunk. Logs and generated C are in this clone under .lane-artifacts. Consumer closure remains pending. Any speedup requires a future matched normal receiving/audit run; the 18.0552s birth time is not claimed as recoverable savings. No existing native pin or active Store is changed by this source repair.
