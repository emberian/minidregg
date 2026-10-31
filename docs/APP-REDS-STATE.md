# app-reds lane: state (2026-10-30)

Lane `lane/app-reds`, worktree `/Users/ember/dev/minidregg-lanes/app-reds`, based on origin/main `c7aa7e8c4`
(local `main` was 1,632 commits behind origin; `lane/spk-fresh` is an ancestor of origin/main).
hbox run area `/ci/ar-ot` (bin = candidate f34b0309 copies, src = this worktree); every world torn down
(`removal_assertions=0`).

## 1. OwnTracks write: FIXED by repackaging (qualified 3/3)

Cause (traced in the fork, mnutt/owntracks-recorder ba4d72ef = ot-recorder 0.6.9): `http.c field()` replaces
`u`/`d`/`user`/`device` with the raw `X-Sandstorm-Username` header, which Sandstorm percent-encodes
(`Grain%20owner`). The write path reduces user and device to a storage name in `util.c ut_lower` (every
non-alphanumeric byte becomes `-`, so `grain-20owner`); `last_users` and the friends list look the raw
lowercased header up unreduced (`grain%20owner`). A recipe cannot fix it: the header overrides every query
parameter on every route. Fix: `apps/packages/owntracks/patches/0001-sandstorm-identity-one-storage-name.patch`
percent-decodes the header and reduces it with the one `storage_name` rule that `ut_lower` now also calls, so
write and lookup name one principal. Mini's display name and routing identity are untouched.

New package (our key, apiPath "/", Debian 13, built from the pinned codeload tarball, patch applied at build):
app `1zzj5zrt8f0vwf5q1rmm09fff9y9684mcq79me6kmjrks1acfmqh`, package `779a8d94e36bf3d481c432100ecc61ad`, version
`0.6.9-1`; key `~/.dregg-secrets/spk-keys/owntracks.key`; forge build dir `/srv/spk-build/owntracks`. The build
smoke (chroot, uid 65534) writes and reads back for `Grain%20owner` and shows a second user does not see it.
Qualified on hbox, attempt 1 in `/ci/ar-ot/qualification-1/rows.tsv`: lifecycle PASS 43 s; POST /pub then
GET /api/0/last returns this run's timestamp, descriptor lists api and web; forged Sandstorm identity headers
refused. OwnTracks is in the local market index fixture; it is not in FEATURED (it never was).

## 2. Hummingbird: native conversation qualification (controller side BUILT; live run OWED)

`featured-qualify.sh` -> `binding.py` drives only http and ddp, so `protocol: conversation` returns
`binding-protocol-unsupported`; DEMO-PATH-STATE says not to add a second Python interpreter, and none was added.
What was missing was the controller's receiving end for the shell: `mini app-interface --action call|qualify`
sends `grain-runtime tool SOCKET hard ID mini_app_<alias>[_<op>|_qualify]`, but `foreground_tool` dispatched only
`mini_application_api` and the Oracle tools. Now (grain-runtime `main.rs`, `typed_applications.rs`,
`application_api_tools.rs`):

- `mini_app_*` names are operator-foreground tools when a typed attachment owns them (the attachment's bound tools
  and the hidden `mini_app_<alias>_qualify`); preflight checks the attachment, the declaration digest the shell sends
  (`_miniInterfaceDigest`, stripped before validation) and the route's Host pin and recorded birth (the route check is
  now one helper, `preflight_application_route`, shared with `mini_application_api`).
- `foreground_typed_application` runs the SDK executor (`call_tool`, or the new `qualify_tool` over
  `Declaration::qualify`) inside the controller; each request it prepares re-enters `foreground_application_api`: one
  fresh admission and settlement apiece, as the Hermes worker's `__mini_typed_http_raw` path does. A lost reply is
  uncertain and never replayed. Trusted context (operation id, time, rendezvous seed) is the controller's; the
  operator's `runId` may not shadow it.
- The controller's application-API method list gained `CONVERSATION` (the Host's lifetime wire already accepts it and
  validates the descriptor body against `protocol/hosted-conversation.json`).

Tests (filtered): `typed_applications` 15 pass on the Mac and on hbox, including the WBO conversation declaration
qualified end to end through the real `raw_arguments` and `parse_input`, and the foreground name, digest and context
checks. The `foreground` filter on hbox: 62 pass, 8 `birth_refusal` tests fail; they drive a scripted
`controlled-mini` through the birth-refusal producer, never reach the typed code, and also fail on the Mac with the
child exiting 3. I did not baseline them (no stash); treat them as the standing birth_refusal environment red until
someone shows otherwise.

OWED, not claimed: the live receiving-path run. It needs a Hermes controller world with Hummingbird attached as a
typed application (the apps-agents j14-apps journey, `docs/APPS-AGENTS-STATE.md`), a rebuilt `grain-runtime`, then
`mini app-interface --action qualify --declaration apps/interfaces/hummingbird.json --attachment hb ...` with its
native receipts and the correlated socket hit retained. Unproven there: that the Host's lifetime reserve plan accepts
the CONVERSATION method code end to end, and the reply shape of a hosted frame batch through `http-v3`. Once that run
exists the same command qualifies the WBO and Scrumblr declarations.

## 3. deploy/spk-host/tests/test_controller_world.py: environment AND stale tests, all fixed

hbox login umask is 0002; the tests create fixture directories under the operator home and custody refuses
group-writable ancestors, so 7 of the 8 errors were the environment. The test now sets its own umask 022
(restored by cleanup). The other 3 (1 error, 2 failures) fail on the Mac too and were stale tests behind
deliberate code: (a) `copy_worker_tree` inventories (and refuses links) before creating the destination, so
the test asserts no destination instead of an empty one; (b) `check_app_allocation` moves a taken START to the
next free aligned range (f8243aba9), so the tombstone test asserts the move and adds the exhausted-delegation
refusal; (c) the operator proxy runs on `ProtectHome=tmpfs` (bind of the upstream directory), which the sibling
test already asserted. Result on hbox: 86 tests OK. On the Mac one error remains, `socket.SO_PEERCRED`
(Linux only).

## 4. FEATURED

- WBO repointed: FEATURED now names `j4jvn386...` (package `d3b06718...`, the qualified wbo-r2 build); it and
  OwnTracks are added to `native/resource-client/tests/fixtures/fresh-local-index-2026-10-29.json`
  (regenerated with `deploy/market/fresh-index.py`; the 20 existing entries are byte-identical).
  `apps/interfaces/wbo.json` rewritten for WBO 2.18.26 (the 1.20 wire was `getboard`/string tools; 2.18 joins by
  `board&baselineSeq=0`, numeric create mutation with clientMutationId, acknowledged by a `mutation` broadcast,
  saved export is SVG). `scrumblr.json` had the same staleness (declared eio3 at `socket.io/`; the package
  serves engine.io 4 at `/socketio`) and is corrected. The native fixture tests in
  `native/mini-sdk/tests/app_interface_knowledge.rs` were red on origin/main (old package ids) and now pass.
  Neither conversation declaration can be live-qualified until item 2 closes.
- Mercurial, Perplexity Sudoku, 3D Blockstack: typed declarations written (`apps/interfaces/mercurial.json`,
  `perplexity-sudoku.json`, `blockstack-3d.json`); their recipes' write rows now run through them. Qualified live on hbox (`/ci/ar-ot`, worlds down,
  `removal_assertions=0`): Perplexity Sudoku 3/3 (typed new/save/read through the declaration, descriptor api+web,
  forged identity refused); 3D Blockstack 3/3 (typed submit/best; the app answers JSON as text/html, so
  `score.best` decodes as text); Mercurial 3/3 (typed read-only `repo.summary` of the empty repo via
  `row.py call`, because the typed qualify gate refuses a declaration with no write, as for Datasette; then the
  hg-wire push read back through raw-file and rev, descriptor api+web). The Mercurial push driver and recipe
  (`apps/packages/mercurial/qualify*`) were only on the hbox lane before; they are now in the repo.

## Scout's parity red (JWF 1/72, "without a face: apps(apps list j)"): FIXED

Not a missing face: `/verb/apps` renders its leaves. `jweb-frontend.sh` split each usage alternative with an
unquoted `for w in $alt`, so `[--json]` was a glob that matched a one-letter file named `j` in the working directory
and turned `apps list [--json]` into `apps list j`. Globbing is now off around the split (ad58a4b9e). Reproduced
the glob in bash; not re-run through the whole JWF step.

## Since the four reds (present state, 2026-10-31; one document, both instances folded)

Landed on `lane/app-reds` (and in staging e1a32a07d unless noted):
- Volumes are project-quota directories, not loop images (111985198, deploy/spk-host/VOLUMES.md), with a
  host-side custodian for user-namespaced containers (d786b5d2c; `spk-host volume-custodian`, `MINI-VOLUME/1`
  line grammar, statements C1 to C6; app uid floor 10000 for a custodian world, 28be1c40c; unit template with
  the literal ROOT written by `install-volume-custodian`).
- Resident /var check (486f0196f, identical in content to 3eceeb77d): the resident runs as the operator and
  holds the app-private 0700 directory only as an O_PATH descriptor, so the project ioctl failed (EBADF) and a
  read reopen failed (EACCES): "resident bootstrap refused: Permission denied". `os::var_filesystem` compares
  `fstatvfs` of the volume with its parent (a project-limited directory reports its limit); the witness pins the
  inode. Evidence: EtherCalc through the full launch 3/3 on hbox (/ci/ar-ec/qualification-8).
- Root-side `controller-tool` accepts `mini_app_<name>` typed tools; controller-world.py is pinned by sha in
  install-user-world (move both together): 6be1c1ea7, b1c30a598. The `vars-backing` bind and the `ingest-scratch`
  directory are in install-user-world (b1c30a598, 45091c14e).
- Intake spool is an operator input (45091c14e): broker config `ingestScratch`, `spk-ingest --scratch`,
  `spk-host materialize --scratch`. Free-space need on the SPK store drops by one decoded bound.
- `grain install` reports signedAppId/signedAppVersion (c730fd3ea): the values go in `signed-identity.json`
  beside `qualification.json`, never in it (resident_service and install_v3 read it with deny_unknown_fields;
  tests in both). Before this every real market install was refused appIdMismatch.
- apps-e2e grant bound 50000 and funding 20000 (f72223652, E7); bend refusal hints (35f008d3d); `responseType`
  in the publication JSON and printed by `bend publish` (32a7f0fc0, Lean: needs the next host build).

hbox state outside git (root host changes, not reboot-persistent):
- ONE prjquota backing: `/tank/lanes/vars-backing.img` (24 GB sparse ext4 -O quota,project) loop-mounted
  `prjquota` at `/var/lib/mini-vars-backing`, named by `/etc/mini-spk-volumes/vars-backing`. After a reboot,
  `sudo mount -o loop,prjquota /tank/lanes/vars-backing.img /var/lib/mini-vars-backing`, or world installs
  refuse by name. (The sibling's duplicate `/var/lib/mini-spk-vars-backing` from `/tank/mini-spk-vars-backing.img`
  was empty; unmounted, detached and removed.)
- `/tank/mini-ingest` (root:root 0755) named by `/etc/mini-spk-volumes/ingest-scratch`: each world's intake
  spools to `/tank/mini-ingest/<store>`. /tank is the HDD mirror, so ingest through it is slower; candidates
  built before 45091c14e ignore the file.

Diagnosed: the Davros control run's `controller-worker-prepare` refusal was my `grain-runtime` copy at mode
0775 under hbox's umask 0002 (custody wants it unwritable by group); the next failures were the root-side tool
whitelist (fixed above) and then the resident /var check (fixed above). gate14's j14 `insufficient scratch
workspace` was hbox's root disk (36 GB free against the operator-appliance profile's 20 GiB decoded bound).
A hard-linked copy of integ/src/.lake is never a build tree: lake writes traces and setup.json in place (I
poisoned two files that way, ObjectivePackageAuthor.setup.json and .trace; the integrator removes them); use
the lane pool (/home/hbox/pool, `lane-tree`, LANE_POOL_NO_WARM=1 while integ builds). Two instances must not
rsync into one hbox src directory; use /tank/lanes/<own>/src.

## Continuation (2026-10-31, written by the instance at its context limit)

On staging already (do not redo): 40efdcff9 (any non-zero u64 resource id), c88b88755 and 4692d6dfb as 5ae0de223
(a final say that never reached the Host is retried, a Host refusal stays terminal), c0a49c8d7, 78a20cb56,
5c4f73459 (refusal clauses), 6cae27559 (gogs fixtures, supersedes ecf4b917d).

Open, in order:
1. H1b cause. `lane/app-reds-codec` 58f0bad2b (grain-runtime codec honours MINI_CODEC_RESIDENT=0) is not on
   staging; the integrator overlays it as dc61016cb-codec and judges it by the criterion: the final say succeeds
   AND the controller journal shows no not-submitted resolution or resubmit for the say's write. Land it by
   sha once that gate says so. A resident daemon forked inside a short-lived controller command is a lifetime
   bug whatever the trace shows: either honour the switch, or start it detached with its own PID file and a
   client that detects a dead pid+socket and restarts it.
2. START fixes the coordinator names: the route socket path over SUN_LEN once app ids are 20 digits, and
   "agent reserve custody lacks confirmation" (native/resource-client/src/agent_reserve.rs field()). Neither is on
   any branch of this lane (checked: lane/app-reds*, origin/lane/app-reds*); the work was not committed or is
   lost. Reproduce from perf-apps' apps-install and app-route measurements (hbox /tank/lanes/perf-apps), then
   fix each by reading the code path: staging has f7f23fb46 (bound route socket paths) and the `confirmation`
   readers at grain-runtime main.rs:1814, :4107, :7007.
3. Refusal-clause sweep, second half. 5c4f73459 landed the first. Uncommitted in worktree app-reds-2 (not
   committed, Lean builds failed at Host/Json.lean:4448 `hexJson` type, Host/ApplicationDispatchReady.lean:73
   `stopped` type): clause names through Host JSON and InspectRender, plus journey rows j12/j12w/j14/jdisclose/
   jpay6. Statement-first: say in the sha message if any refusal type changes. Build in the lane pool
   (/home/hbox/pool/bin/lane-tree acquire app-reds origin/integration/staging, LANE_POOL_NO_WARM=1, swarm-build
   at 24G or less); keep PID files and logs in your own tree or /ci/<you>, never the pool root.
4. Live Hummingbird run, then WBO and Scrumblr, on a current ready candidate via gate12's j14apps().
5. E3/E4 (why names the clause; guard rejection detail as hex) fold into item 3; E7 is the world-up/harness
   question; the decider-side half of G2; the Hermes worker interpreter (built 3.12, box has 3.13); op66-plan
   for EtherCalc and Etherpad on the demo world after infra's rebuild (keep the retained plan).
6. Remove /tank/lanes/app-reds/target-rel (integrator rule: no new data on /tank).

Uncommitted edits in worktree app-reds (volume custody, os.rs, jdisclose, main.rs) are not this lane's.
Base new work on origin/integration/staging (branch lane/app-reds-cont).
