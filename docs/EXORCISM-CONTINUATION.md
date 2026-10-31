# Exorcism: continuation (start here)

Lane `lane/exorcism`, worktree `/Users/ember/dev/minidregg-lanes/exorcism`. The findings table and
every landed batch with its numbers are in `docs/EXORCISM.md`. Integrator: aba0beaa578594e92.
Hot-path (a6c4a1532687a4fdb) owns submit, FORMAT, `issuerCheck` (`existsSupport`), the
ServedAuthority projection and the Store/consent first-open decode (its row 11). Perf-client
(a8d456c6e773efbb8) owns the residents (never idle since 86428a2f1) and the consent provider. This
lane owns the per-request cost of a signed read, aiming at ember's bar of about 1 ms warm.

## Measured: batch 6 (74e1cfa10) against batch 5 (1c151fce4)

Scratch worlds on hbox, member-1 `doc show` through each world's own ssh wrapper; CPU from /proc
over 100 warm reads; per-op client-side MINI_TRACE medians over 30.

| per signed read | batch 5 | batch 6 |
|---|---|---|
| wall | 42.2 ms | 32.4 ms |
| operator CPU (Host + Store helper) | 27.8 ms | 15.0 ms |
| consent provider CPU | 2.2 ms | 1.9 ms |
| codec resident CPU | 4.1 ms | 3.8 ms |
| op 144 key status | 5.76 ms | 1.07 ms |
| op 4 challenge | 1.73 ms | 1.43 ms |
| op 5 signed read | 6.41 ms | 5.66 ms |
| `doc show` line inside mini | 23.9 ms | 17.7 ms |

A cold verb (residents not running) was 555-866 ms on batch 5; residents no longer idle out.

## Op 5 on the batch 6 Host (perf, 40 reads, inclusive share of dispatchSession)

- `checkGrants` 60%: `ResourceObservationAdmission.check` 49%, of which
  `capabilityEvidenceChecked` 19% and `issuerCheck`'s `DFinsupp.support` 15% (hot-path's
  `existsSupport` removes the latter; it was not in batch 6).
- `NativeObservationController.challenge` recomputed inside op 5 (`authorizeAuthenticated`) 13%:
  op 4 computed the same challenge; op 5 recomputes it to check the answer.
- `PolicyComponentResolution.loadRoots`/`loadPolicy` 12% (re-encodes each policy record through
  `fetchPolicySource`).
- `ResourceObservationAdmission.step` 10% (after hot-path's demand projection).
- Encodes spread across: `resourceViewUsing` re-encodes the cell for its bytes (`PackedCell.decode`
  builds cells with `materialize`, not `materializeCanonical`, so the Store's own bytes are dropped);
  `signedRequestBytes` re-encoded for each signing header.

### Read-path Lean fixes: written, not yet in a Host build

- `fetchPolicySource` encoded each policy record twice (digest, then bytes); `fetchPolicySourceFast`
  encodes once (`@[csimp] fetchPolicySource_eq_fast`, Compiler/CanonicalCellRegistry.lean).
- `loadPolicy` re-encoded the record it had just decoded to check its digest; it hashes the
  fetched bytes instead (canonical, so the same digest), Compiler/CredentialAuthorityPolicyRegistry.lean.
- Build them (with whatever else is ready) through iteration speed's `lane-tree host` once it is
  announced; do not build in t7 before then.

### Next, written up but not started

- **Done (not yet built):** the law graph loaded twice per grant (`keys` through `predicateOf?`,
  then `resolve?`). `authorizeCheckedFast` loads it once (`lawGraph`), derives the keys and the
  step from it, and resolves on it (`resolveWith`); `@[csimp] authorizeChecked_eq_fast`. The head
  policy is still loaded once beside the graph's own load of it (about 1%).
- `headerAt` runs twice per grant (in `challengeAt` and again in `checkGrant`), about 3%.

Next candidates, in order of share: a verdict cache for `checkGrants` keyed by everything it reads
(authority root, policy roots, resource cell root, clock, grant bytes); `PackedCell.decode` keeping
the decoded bytes (`materializeCanonical`, already proved equal); `loadPolicy` keeping the decoded
record next to the bytes it was decoded from.

## Client side on batch 6 (perf stat over 30 warm `doc show`, world /ci/exo/w6)

- With the deployed wrapper (dregg-infra's copy: `#!/usr/bin/env bash`, readlink, dirname x2,
  basename per verb): 12.4 ms client CPU, 25.5 ms wall. With staging's wrapper (perf-client
  b34173dad, batch 7): 6.5 ms, 18.5 ms. Infra installs the candidate's wrapper from batch 7 on.
- What is left in `mini` (about 5.5 ms CPU, half of it kernel: exec, dynamic loading, page faults):
  attempt-file writes (`durable::staged`) about 15%, reads about 4%.
- So a warm one-shot read is about 18 ms: Host ops 8.2 ms (op 144 1.1, op 4 1.4, op 5 5.7), codec
  3.5 ms CPU, consent 1.9 ms CPU, client 6.5 ms CPU.

## Building a Host to measure a Lean change

A native Host build takes about 48 minutes in a pool tree prepared with `lane-tree native`
(hot-path's recipe: `/ci/hpc/nb/build7.sh`, tree t7, artifacts in `/ci/hpc/nb/artifacts`; hotpatch
with `/home/hbox/lanes/integ/hotpatch-candidate.sh <base> <name> minidregg-host=...`, see
docs/HOT-PATH-STATE.md). This lane has not built one.

## Other open items

- The client's attempt-file bus: about 60 openat per signed read (it writes each step and reads it
  back; `config.json` about eight times).
- Codec frames: the view is decoded twice (view-resource, then view-document).

## Rules carried

PID files and timeouts for every remote job; stop only by PID file; named-file commits with
`git commit -F`; filtered tests; swarm-build; no Host build on hbox (the integrator builds
candidates); `/home/hbox/lanes/exorcism` is the Rust-only clone; scratch worlds via
`jworld-scratch.sh up/down` with distinct ports; `/ci/exo/cpu.sh` and `/ci/exo/ops.sh` are the
drivers; no pool tree is leased (`lane-tree acquire exorcism REF` for a Lean check).
