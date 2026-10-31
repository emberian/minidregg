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

## Since the four reds (2026-10-30 evening): what is landed, what is owed

Landed on `lane/app-reds` (shas in order): 111985198 volumes are project-quota directories, not loop images
(deploy/spk-host/VOLUMES.md); d786b5d2c the host-side volume custodian (`spk-host volume-custodian`, versioned
`MINI-VOLUME/1` line grammar, statement C1 to C6) and 28be1c40c app uid floor 10000 for a custodian world;
6be1c1ea7 + b1c30a598 the root-side controller-tool accepts `mini_app_<name>` typed tools (controller-world.py
pin moved in install-user-world) and the vars-backing bind in install-user-world; f72223652 apps-e2e grant bound
50000 (E7: the birth was refused no-grant at 1000); 35f008d3d bend refusals name the package already published and
the response-type rule (G1, G2 partly); 45091c14e the intake spool directory is an operator input.

hbox state I set up (not in git): `/tank/lanes/vars-backing.img` (24 GB sparse ext4, project quota) loop-mounted at
`/var/lib/mini-vars-backing`, named by `/etc/mini-spk-volumes/vars-backing`; the mount is not in fstab, so a reboot
loses it and `install-user-world` then refuses by name. `/tank/mini-ingest` (root:root 0755) named by
`/etc/mini-spk-volumes/ingest-scratch`: each world's intake spools to `/tank/mini-ingest/<store>`; /tank is the HDD
mirror, so ingest through it is slower; candidates built before 45091c14e ignore the file.

Diagnosed: the Davros control run's `controller-worker-prepare` refusal was my `grain-runtime` copy at mode 0775
under hbox's umask 0002 (custody wants it unwritable by group); `/ci/hb-data/run.sh` installs it 0555. The next
failure was the root-side tool whitelist (fixed above). gate14's j14 `insufficient scratch workspace` was hbox's
root disk (36 GB free against the operator-appliance profile's 20 GiB decoded bound), not a layout or version
mismatch.

Owed: the live Hummingbird run (the foreground typed/_qualify tools are built and unit-tested; the rerun needs a
current candidate, the old one was swept), then WBO and Scrumblr; `op66-plan` for EtherCalc and Etherpad on the demo
world (waits for infra's rebuilt forge world, with the retained plan kept); E3 and E4 (why-clause and guard-rejection
rendering, Lean/Host side, no owner); the G2 slot response type query; E7's live rerun on the explorer's side.

Hazard: another process edited this worktree (resident `/var` check: os.rs, resident_launch.rs, volume_custody.rs,
the fixture rename, the custodian unit template) and left it uncommitted; I did not take it.
