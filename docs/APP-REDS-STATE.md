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

## 2. Hummingbird: native conversation qualification (NOT DONE; gap named)

`featured-qualify.sh` -> `binding.py` drives only http and ddp, so `protocol: conversation` returns
`binding-protocol-unsupported`; DEMO-PATH-STATE says not to add a second Python interpreter. The native
executor (`mini_sdk::app_interface::Declaration::qualify/execute`, `app_interface_transport.rs`) and the Host's
CONVERSATION method (`spk-host/src/hosted_conversation.rs`, accepted by the lifetime API wire) both exist. What
is not attached is the controller's receiving end for the shell: `mini app-interface --action call|qualify`
sends `grain-runtime tool SOCKET hard ID mini_app_<alias>_qualify`, but `grain-runtime` `foreground_tool`
(main.rs) dispatches only `mini_application_api` and the Oracle tools; typed tools run only inside the Hermes
MCP worker (`typed_applications::call_tool` through `__mini_typed_http_raw`). There is no hidden `_qualify`
foreground tool, and no foreground typed tool. Closing it is a grain-runtime feature (a foreground typed executor
whose per-request callback re-enters `foreground_application_api`, with its one-reservation-per-attempt journal
invariants), then a j14-apps-style world with Hummingbird attached. See the report to the integrator.

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

## Not this lane

Scout a3d575cdd7a822f6b reports the demo row JWF failing 1/72 on web parity: verb `apps` (`apps list j`) has no
visual web face (hook.out at hbox:/ci/scout/ev/demo/JWF). Not one of the four reds; routed to the integrator.
