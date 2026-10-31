# Seat: read-path

Agent: a97dba51f72535cb9 (the exorcist, distilled once)
Worktree: /Users/ember/dev/minidregg-lanes/exorcism (detached on `main`; commits push to `main`)
Owns: The Host's read and query ops (op 4 challenge, op 5 signed read, the read half of op 144), the codec
resident and its read inspections, the client's read path (`Flow::query`, `query_retained`, `signed_view`,
`read_scratch`, the read file bus `mini_sdk::attempt`), `doc show` and `doc history` rendering.
Quest: a warm signed read toward ~1 ms, widest costs first: cold first read (3.9 s), restart plus first read
(~5 s, shared with host-execution's restart), then the Host's signed read (~5 ms).

## Where a warm `doc show` stands

hbox /ci/exo/w8 (batch 7 Host overlay with the read-path Lean fixes, the lane's client), member-1, through
`mini-line` and the line resident. hbox load moves these more than any one change: compare only alternated
rounds, and move measurement to persvati's standing world when it exists.

| part | cost | owner |
|---|---|---|
| wall end to end, load 9-19 | 5.6-8.4 ms (8.0-9.6 ms single runs) | |
| op 5 signed read | about 5 ms at load 27 | read-path (Lean) |
| op 4 challenge | about 2.2 ms at load 27 | read-path (Lean) |
| op 144 key status | once per command (member-side's d035d8250) | member-side |
| consent provider | 2 x 1.2 ms | member-side |
| codec CPU | 2.9-3.2 ms (load 22-25) | read-path |
| line resident task-clock | 1.0-2.1 ms | read-path |
| `whoami` wall, low load | 1.1-1.3 ms | member-side |

## Landed (all on `main`)

- 3822c09f2, d843f2ef6: `bin/mini-line` is the ssh forced command (six absolute arguments; 64 usage, 66 mini
  not executable, 78 bad /etc/mini/session-* or peer.pins, 75 a third call); deploy/shell/mini-shell-ssh deleted.
  Anchors default to $home/.mini/consent-anchors whenever MINI_CONSENT_ANCHOR_DIR is unset. Infra e29997d installs
  it as /usr/local/lib/mini/mini-shell-ssh on every ship. `whoami` wall 4.86 to 2.46 ms, `doc show` client CPU
  5.12 to 2.71 ms (8 alternated rounds, load 20-27). Tests: tests/mini_shell_ssh.rs.
- 478f170ab: reference names read lazily, once per read. 500 references: resident CPU 13.4-15.0 to 2.8-3.2 ms.
  Still O(references) for a page that names a target; the maintained index is store-retained's node (keyed per
  file, not on the directory stamp: in-place overwrites and same-tick creates do not move it).
- 837c3f457: `read_scratch::retain`; `doc protect`'s enrollment phase stays inside the workspace (batch 8
  documents:protected row 3, "phase must remain inside participant workspace").
- 56d65ae3c: the read file bus. `mini_sdk::attempt::Attempt`: disk for writes (custody record unchanged), memory
  for reads, written out only on a path request (`path`/`output`/`on_disk`) or a failure (`materialize`). `Flow`
  runs over it; `Local` is bytes; read-path codec inspections are `inspect_bytes`. Per read: openat 53 to 16,
  write 30 to 4, unlink 15 to 0, linkat 13 to 0; resident CPU 3.5-4.4 to 2.6-3.9 ms.
- dde0f4463: a fresh memory attempt asks the disk nothing (statx 57 to 44 per read).
- 697d8dd4f: `doc show` leaves an identical seen/NAME.json in place (its rename was 9% of the resident on ZFS).
  Resident task-clock 2.0-2.3 ms before the bus, 1.0-2.1 ms after these.
- Earlier, with numbers in docs/EXORCISM.md: the codec's one-decode `view-resource-document` (bc17cef1b,
  7e6850892), `mini line-resident` (4336fd84d, 50de20db5, def44636b), `read_scratch` (7dd2f7eda), and Lean
  47b7cb2e1, c763e3ead, 975491262 (`fetchPolicySourceFast`, `loadPolicy` hashing fetched bytes,
  `authorizeCheckedFast` loading the law graph once).

## Next, widest first

1. Cold first read and restart (traced 2026-10-31): both are the FULL Store open
   (`DurableReceiverIO.loadChained`/`load`), O(height) even with the checkpoint at the head. hbox batch 9 world
   /ci/c-997905/w, head 256 (`minidregg-host CONFIG store-bench`, MINI_OPEN_TIMING=1): full open 1,100 ms (read
   all entries 257, fast-forward 91, gate and rebuild 752: every tag from 0, every record decoded 264, the chain
   over every record 111, image, six indexes, rootLog); `validateLoaded` 84 ms. The light open
   (`DurableServed.openHead`, checkpoint + suffix) is 125 ms (checkpoint decode and tree 96), `validateServed`
   82 ms. About 4.3 ms per record: PERF-CLIENT row 14's 3.9 s at height ~920 is the same open.
   Who pays it: `NativeHostSession.start` (`openExisting`, then a light start beside it; `refresh` keeps both),
   and the consent provider's `verifyInitial` (ClientConsentCore.lean:305) though CONSENT-STORE starts it at the
   checkpoint. Both stay on the full shape because the native admission (`NativeHostReplay`, `Opened`,
   `SuffixVerified`) and the session's receivers are typed over the full `Loaded` (KN2 stage 2a). The fix is
   KN2 stage 2b for these two paths: the Host session and the consent admission over the `Opening`. Constant
   factors inside the full open (decode about 1 ms per record) do not change its order and are not taken.
2. Op 5 (Lean; native Host build through native-loop, about 7 min in a pool tree). Perf shares of
   dispatchSession over 40 reads on the batch 6 Host: `checkGrants` 60% (`ResourceObservationAdmission.check`
   49%, `capabilityEvidenceChecked` 19%); the challenge recomputed inside op 5 (`authorizeAuthenticated`) 13%
   though op 4 computed it; `loadRoots`/`loadPolicy` 12%; `step` 10%; `headerAt` twice per grant about 3%;
   `PackedCell.decode` building with `materialize` and dropping the Store's bytes (`materializeCanonical` is
   proved equal); `signedRequestBytes` re-encoded per signing header. Retained form: a `checkGrants` verdict
   maintained against what it reads (authority root, policy roots, cell root, clock, grant bytes), not a cache
   recomputed per request.
3. Codec: `challengeJson` 10% and GMP `Nat` churn in `StreamCodec`.
4. "Reads keep nothing per read" (RULINGS): a read still appends one read-journal line, rewrites seen/NAME.json
   when the world moved, and a refused read moves into attempts/. Decide each against the ruling.
5. Resident statx 44 per read: the pinned config (16) and the Host image (10) re-checked per codec frame and
   session op within one command.
6. Twins on files: `query_batch_once` (main.rs) and participant_enrollment's observation hand-roll the observe
   step beside `Flow::observe`; fold them onto `Flow` over a memory attempt. Chat keeps its newest read per label
   on disk on purpose (`chat::signed_read`).

## Seams

- member-side (a778bbda6509944a5): consent cost per read; mini-web-spawn's `delegated_consent_env` twin of
  mini-line's selection (theirs, by a shared `#[path]` source); op 144 head-keyed check later.
- store-retained (a9b54e85e4a194b91): the reference-name index over WORKSPACE/refs.
- host-execution (a0fee5643746e520c): `issuerCheck`/`existsSupport`, FORMAT, the restart path, the GET read-path
  contract.
- infra (aa72653a8ce442178): deletes edge/mini/shell/mini-shell-ssh once no supported candidate lacks
  bin/mini-line.

## Tools

hbox: Rust-only clone /home/hbox/lanes/exorcism (src, target); scratch worlds /ci/exo/w6, w7, w8 (jworld-scratch.sh
up/down, distinct ports). Drivers in /ci/exo: `tc.sh` (resident task-clock per read, alternated), `rc.sh`
(resident CPU from /proc), `sc.sh` (strace -c of the resident), `fx.sh DIR` (behaviour: reads, writes, history, a
kept read, a refused read), `wr.sh`/`wr2.sh` (wrapper wall and client CPU). Install each build into a new
/ci/exo/<name>-ssh/bin: `cp` onto a binary a resident runs fails with ETXTBSY. No pool tree is leased.
