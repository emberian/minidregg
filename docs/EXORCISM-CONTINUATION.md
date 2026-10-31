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

## Client and codec, measured on /ci/exo/w6 (batch 6 world, `doc show`)

- Client (wrapper + `mini`), perf stat over 40 runs: about 7-10 ms CPU per command, two thirds
  kernel. `mini`'s kernel time by syscall handler (kallsyms via sudo, perf dwarf): user 25%,
  openat 17% (mostly creating attempt files), page faults 14%, exit_group 8%, write 5%,
  linkat/mkdir/rename/unlink/statx 10%. A signed read writes about 15 files (a new
  `attempts/a-N` tree, `sources/q-N.json`, `seen/`), each through a temp name, link and unlink,
  and keeps them: member-1 already holds 520 attempt directories (18 MB). They are receipt
  evidence (`receipt_continuity`), so dropping them is a product decision, not a perf fix.
- Binary layout: fat LTO + one codegen unit (19.6 MB against 21.2 MB) and non-PIE each moved CPU
  by under 10%, within box noise; LTO costs 245 s against 43 s per release build. Not taken.
- A bare `mini --help` is 1.5 ms and 168 page faults; a one-shot process per command cannot reach
  1 ms. A per-member resident behind the ssh wrapper (as `mini command-resident` already is for
  the controller: `workspace list` 0.4 ms framed) is the route.
- Codec resident per doc show (perf over 40): `resourceJson` 23% and `documentJson` 23% of busy
  time (the view decoded and rendered twice: `view-resource`, then `view-document` from the same
  bytes), `challengeJson` 10%, GMP `Nat` churn throughout `StreamCodec`. Lean; batch onto a
  Host build.

## Landed on the lane after batch 8's shas (decisions A and B, root 2026-10-31)

- 4336fd84d + 50de20db5 + def44636b, A: `mini-line` and `mini line-resident`. The ssh wrapper
  execs `mini-line`, which holds the call slot and passes the line and its three descriptors
  (SCM_RIGHTS) to the resident for that slot (two per member, keyed by mini's identity, the
  arguments, MINI_*/HOME/PATH and the umask). The candidate ships `bin/mini-line` (role miniLine,
  family with mini). On /ci/exo/w6: client CPU 6.2 to 2.2 ms per `doc show`, `whoami` wall 3.4 to
  2.5 ms (the bash wrapper's own start is now most of it).
- 7dd2f7eda, B: `read_scratch`. Reads and codec inspections work in a per-process directory on
  /dev/shm or XDG_RUNTIME_DIR (newest 64 kept, removed at a one-shot command's end); a refused read
  moves into attempts/; one read-journal line per read, listed by `history all`. A `doc show` used
  to add 3 attempt directories and 1.5 source files; now none.
- End to end on /ci/exo/w6, 40 `doc show` each, alternated: wall median 23.8 / 24.2 ms before,
  20.6 / 23.1 ms after; minimum 17.4-17.9 ms before, 13.7-16.0 ms after. Of what is left: Host
  ops about 8 ms, codec 3.5 ms, consent 1.9 ms, the resident's own work 3.5-4 ms, the bash
  wrapper about 2 ms.
- Next on the client: the wrapper itself in Rust (its `read`s of /etc/mini files and the pins
  file into `mini-line`), then the in-process file bus (the query path passes paths between
  `author`/`inspect`/`host_files`; bytes would remove the remaining scratch writes).

## Codec double render: done (bc17cef1b + 7e6850892), measured with the read-path Lean fixes

`inspect view-resource-document` (Host/Json.lean `resourceJsonOf`/`documentOf`, one decode) answers
a current page's resource view and its document together; `workspace::signed_page` asks for it and
`rendered_document` renders again only against source pages. Built through native-loop on
acc7cfa03 (overlay `/home/hbox/pool/lanes/exorcism/candidates/acf55bf9d552`, 1275 s) with
47b7cb2e1 + c763e3ead (+ the admitOwn follow-up 975491262). Scratch worlds /ci/exo/w7 (batch 7)
and /ci/exo/w8 (the overlay), 100 `doc show` each, alternated, hbox load 22-25:

| per read | w7 batch 7 | w8, batch 7 client | w8, lane client |
|---|---|---|---|
| wall | 35.5 / 30.0 ms | 31.0 / 27.5 ms | 28.5 / 24.0 ms |
| operator CPU (Host + Store) | 14.6 / 13.0 ms | 12.6 / 11.8 ms | 12.6 / 11.4 ms |
| codec CPU | 4.0 / 3.8 ms | 4.2 / 3.5 ms | 3.2 / 2.9 ms |
| consent CPU | 1.8 / 1.5 ms | 1.8 / 1.5 ms | 1.7 / 1.5 ms |

## The ssh wrapper is the binary: done (3822c09f2 + d843f2ef6), infra e29997d

`bin/mini-line` takes the forced command's six absolute arguments and does everything the bash
wrapper did; deploy/shell/mini-shell-ssh is deleted. Infra e29997d installs the candidate's
bin/mini-line as /usr/local/lib/mini/mini-shell-ssh on every ship and in jworld-scratch; infra keeps
its own edge/mini/shell/mini-shell-ssh only for candidates without mini-line (batch 4, batch 7) and
deletes it once batch 8 is the demo baseline. One rule changed against the old lane copy: the
anchors default to $home/.mini/consent-anchors whenever MINI_CONSENT_ANCHOR_DIR is unset (infra's
F1 fix), not only when HOME is unset. Tests: tests/mini_shell_ssh.rs (6; 30 consecutive runs green
on hbox after the ETXTBSY lock); the python launcher/provision/stage tests green on hbox.

Measured on /ci/exo/w8 (batch 7 overlay world), member-1, 8 alternated rounds of 60 each, hbox
load 20-27, client CPU = wrapper + mini-line + the driver's own per-iteration fork (residents not
counted). Median (minimum):

| per op | bash wrapper + old mini-line | mini-line as the wrapper |
|---|---|---|
| `whoami` wall | 4.86 (3.77) ms | 2.46 (1.67) ms |
| `whoami` client CPU | 4.60 ms | 2.16 ms |
| `doc show` wall | 23.0 (14.8) ms | 18.9 (12.0) ms |
| `doc show` client CPU | 5.12 ms | 2.71 ms |

Driver: /ci/exo/wr.sh WORLD N ROUNDS (before bins /ci/exo/before-ssh, after /ci/exo/after-ssh).

Open twin found on the way (not this lane's surface, told perf-client): mini-web-spawn's
`delegated_consent_env` re-derives the wrapper's delegated-consent selection.

## Reference names read only when asked: done (478f170ab)

`doc show` read every WORKSPACE/refs file twice per read (`rendered_document` and `read_rendered`
each built the target-to-name map). The renderer now asks a lazy `WorkspaceNames`, shared by both
renderings of one read: a page that names nothing reads no reference, one that names something
reads them once. Resident CPU per `doc show` on /ci/exo/w8 (`/ci/exo/rc.sh N ROUNDS DIR...`, three
alternated rounds): member-1 with 13 references 2.3 / 2.3 ms (no difference at that size); with 500
extra references 13.4-15.0 ms before, 2.8-3.2 ms after. Still O(references) for a page with a link
or a transclusion: a maintained target-to-name index is retained-mode work (told a9b54e85e4a194b91).

At low load (16-20) a warm `whoami` through the binary wrapper is 1.1-1.3 ms wall
(/ci/exo/wr2.sh with BDIR/ADIR).

## The read file bus: done (56d65ae3c)

`mini_sdk::attempt::Attempt` holds an attempt's named files: on disk as each is made for a write
(the custody record, unchanged), in memory for a signed read, written to its directory only when
something needs a path (a one-shot Host, a caller handing the signed observation on by path,
`on_disk`) or all at once when the read fails (`materialize`, before the refusal is retained and
`read_scratch::keep` moves it). `Flow` runs over it; `Local` is bytes, `Operator` gets the attempt
and names. Read-path codec inspections are `inspect_bytes` (no input/output files). Per warm
`doc show` (resident, strace -c over 20 on /ci/exo/w8): openat 53 to 16, read 75 to 25, close 61
to 24, write 30 to 4, unlink 15 to 0, linkat 13 to 0. Resident CPU 3.5-4.4 ms before against
2.6-3.9 ms after, lower in each of 6 alternated rounds (load 32-46; `/ci/exo/rc.sh`,
`/ci/exo/sc.sh` for the syscall count, `/ci/exo/fx.sh DIR` for the behaviour checks). Install each
hbox build into a NEW directory: `cp` onto a binary a resident runs fails with ETXTBSY and leaves
the old one in place.

Twins still on files (not yet folded into `Flow::observe`): `query_batch_once` (main.rs) and the
enrollment observation in participant_enrollment.rs each hand-roll the observe step; chat keeps
its newest read per label on disk (`chat::signed_read`, materialized on purpose).

## Next: what is left of a `doc show`

- statx 57 per read in the resident: `host_selection::select_semantic` stats the Host image on
  every codec frame, and other per-op metadata checks. Find which are re-validating something
  that cannot have changed within one command.
- Host ops about 8 ms (op 144 1.1 once per resident until perf-client's d035d8250 makes it per
  command again, op 4 2.2, op 5 5.1 at load 27): `checkGrants`, the recomputed challenge,
  `loadPolicy`; the read-path Lean fixes are written, see above. Consent 2 x 1.2 ms (perf-client).

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
