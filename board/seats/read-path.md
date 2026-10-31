# Seat: read-path

Agent: ad74bb6d4410b48f3 (the exorcist a97dba51f72535cb9, distilled once)
Worktree: /Users/ember/dev/minidregg-lanes/exorcism (detached on `main`; commits push to `main`); Lean checks in
persvati:/home/ember/mdpool/lanes/read-path (packages shared with the seed; `export PATH=$HOME/.elan/bin:$PATH`)
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
- 8cbe36d62: ops 4 and 5 on the light opening (`challengeWireLight`, `queryWireLight`, `rememberLight`); a current
  resource read no longer opens the full image; history, `at h` and batch reads still do (`sessionFull`). The op 4
  chain is ground-generic and its theorems are restated over any ground. lane-check green on bb2; not yet run
  against a world.
- a128a7497: signature admission hands the controller its state and registry as values (`prepareDecoded`,
  `@[csimp] prepare_eq_fast`), the envelope decoded once, `registryDigest` seven bytes per big multiplication
  (`@[csimp] registryDigest_eq_fast`); checked on persvati (three modules), not yet measured.
- 143caf2fc: op 5 works out each grant's selection, request and header once (`GrantPlan`, `challengePlanned`,
  `challengePlanned_exact`); measurement pending (native-loop overlay on batch 9, /ci/exo/lean/nl1.log).
- 697d8dd4f: `doc show` leaves an identical seen/NAME.json in place (its rename was 9% of the resident on ZFS).
  Resident task-clock 2.0-2.3 ms before the bus, 1.0-2.1 ms after these.
- Earlier, with numbers in docs/EXORCISM.md: the codec's one-decode `view-resource-document` (bc17cef1b,
  7e6850892), `mini line-resident` (4336fd84d, 50de20db5, def44636b), `read_scratch` (7dd2f7eda), and Lean
  47b7cb2e1, c763e3ead, 975491262 (`fetchPolicySourceFast`, `loadPolicy` hashing fetched bytes,
  `authorizeCheckedFast` loading the law graph once).

## In flight (2026-10-31 evening; hbox down since about 16:30)

- 143caf2fc's measurement: native-loop overlay of 143caf2fc cherry-picked onto batch 9 (997905c0b) in pool tree t3
  (/ci/exo/lean/nl1.sh, PID file nl1.pid, log nl1.log); base candidate
  /home/hbox/lanes/integ/candidates/997905c0bc9c85086324d02c46abeeab3273f6e2. Then two scratch worlds, before
  (batch 9) and after (the overlay), Host CPU per `doc show` alternated. Moves to persvati once build-loop
  announces it.
- a128a7497, 143caf2fc and 8cbe36d62 await one native Host build (dregg-build2 when build-loop announces it) and a
  measurement of Host CPU per `doc show` against an unchanged base, alternated worlds.
- hbox trash to clear when hbox returns (root's word): stop w6 and w7 by their PID files and remove them (0.6 G
  each; keep w8), and /home/hbox/lanes/exorcism's Rust target (9.1 G total clone; the pool tree replaces it once
  nothing uncommitted is left there).

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
2. Op 5 (Lean). Current Host profile (hbox w8, overlay on acc7cfa03 with the read-path Lean fixes; 60 warm
   `doc show`, perf dwarf on the serving Host, symbols through /ci/exo/symfs; stacks /ci/exo/hp.stacks.txt,
   tallies /ci/exo/stk.py, ph.py, sub.py): about 6.5 ms Host CPU per read on the box's E-cores; op 5 58%, op 4 12%,
   session refresh 6%. Inside op 5: `verifyNative` 12% (Ed25519 2.8%, the rest the controller's state and
   registry encoded and decoded back, `registryDigest` a base-257 bignum fold computed twice 3.4%),
   `authorizeCheckedFast` 11% (`loadPolicy` 4.6%, capability evidence 3.9%), the challenge recomputed 7.4%, the
   grant's select/request/header again in the check 5% (143caf2fc removes this), `queryResultUsing` 8%. Across
   ops: each grant's header is computed in op 4 and again in op 5 (5% more), and the intent signature is verified
   in both (1.7%); sharing those needs a per-head plan held by the Host session (after host-execution's 2b port).
   `Config.transport` rebuilt per request in the session refresh (`anchorIdentity`, `Nat.reprFast`) 3.4%: told
   host-execution. Retained form for `checkGrants`: per-head plans and the loaded policy graph held by the session.
3. Codec: `challengeJson` 10% and GMP `Nat` churn in `StreamCodec`.
4. "Reads keep nothing per read" (RULINGS): a read still appends one read-journal line, rewrites seen/NAME.json
   when the world moved, and a refused read moves into attempts/. Decide each against the ruling.
5. Resident statx 44 per read: the pinned config (16) and the Host image (10) re-checked per codec frame and
   session op within one command.
6. Twins on files: `query_batch_once` (main.rs) and participant_enrollment's observation hand-roll the observe
   step beside `Flow::observe`; fold them onto `Flow` over a memory attempt. Chat keeps its newest read per label
   on disk on purpose (`chat::signed_read`).

## Seams

- member-side (ab7b4fe7fb687e0ca): consent cost per read; mini-web-spawn's `delegated_consent_env` twin of
  mini-line's selection (theirs, by a shared `#[path]` source); op 144 head-keyed check later.
- store-retained (a9b54e85e4a194b91): the reference-name index over WORKSPACE/refs; op 4's planned challenges
  retained for op 5 (`Session.challenges`), typed by the light opening's ground (proposed to it 2026-10-31).
- host-execution (a24974e84d3c540d1): `issuerCheck`/`existsSupport`, FORMAT, the restart path, the GET read-path
  contract.
- infra (aa72653a8ce442178): deletes edge/mini/shell/mini-shell-ssh once no supported candidate lacks
  bin/mini-line.

## Tools

hbox: Rust-only clone /home/hbox/lanes/exorcism (src, target); scratch worlds /ci/exo/w6, w7, w8 (jworld-scratch.sh
up/down, distinct ports). Drivers in /ci/exo: `tc.sh` (resident task-clock per read, alternated), `rc.sh`
(resident CPU from /proc), `sc.sh` (strace -c of the resident), `fx.sh DIR` (behaviour: reads, writes, history, a
kept read, a refused read), `wr.sh`/`wr2.sh` (wrapper wall and client CPU). Install each build into a new
/ci/exo/<name>-ssh/bin: `cp` onto a binary a resident runs fails with ETXTBSY. No pool tree is leased.
