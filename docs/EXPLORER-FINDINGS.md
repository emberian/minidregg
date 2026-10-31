# Explorer findings

Present-state table, rewritten whole at each batch. Lane `lane/explorer`. Subject: candidate
be4ef7510 (hbox `/home/hbox/lanes/integ/candidates/be4ef751074ca28c7d306c2f2bcf61cda03893c8`),
explored as test members only. Batch 13, 2026-10-31.

## Worlds (all on hbox, all mine; torn down when the lane ends)

| world | what | how it was made | down |
|---|---|---|---|
| `/ci/x1/w` | scratch Store + 4 hosted members + ssh front (port 22650), default jworld genesis (no Objective policy) | `/ci/xp-log/up.sh` = `jworld-scratch.sh up` (dregg-infra-69c17a3) under the world-up flock | `jworld-scratch.sh down /ci/x1/w`; PID files under `/ci/x1/w/pid` |
| `/ci/x2/w` | same, with the demo's `genesis-params.json` plus `objectiveInvocation` authored by `scripts/author-objective-policy.sh` (HOTPATCH, see E1) | `/ci/xp-log` + `up2.sh`, port 22670 | `jworld-scratch.sh down /ci/x2/w` |
| `/ci/xw1` | standing grain world (broker, workroom) | `scripts/spk-platform/world-up.sh` with the candidate's bin as base and own | `scripts/spk-platform/world-down.sh /ci/xw1`; worker PID `/ci/xe2e2/worker.pid` |
| `/ci/xweb` | mini-web-spawn (dev) + mini-web gateway on 127.0.0.1:22660 over x1's members alice/bob/carol | `/ci/xp-log/web.sh` | PIDs `/ci/xweb/helper.pid`, `/ci/xweb/gateway.pid` |

Driver: `/ci/xp-log/m MEMBER 'verb args'` runs a shell verb as a hosted member over the forced ssh
(`m2` for x2). One caution for anyone reusing it: ssh joins argv with spaces, so pass the whole
verb line as ONE quoted argument or `say hello --in room` becomes the text "hello --in room".

## Faults

| id | where | repro | evidence | owner | hotpatch |
|---|---|---|---|---|---|
| E1 | `bend` on the demo genesis | (a) `mini bend publish tally @Tally.obend --entry tally` as a member of a world whose genesis is `dregg-infra edge/demo/genesis-params.json`: `refused: ... Refusal.packageType "this deployment registers no Objective policy"` (that file has no `objectiveInvocation`; `scripts/author-objective-policy.sh` exists to make it). (b) with the policy pinned, `bend run tally tobj --input ... --deposit 100` costs 30,543 (birth envelope 30,443) and a freshly enrolled member holds 993 of the door's fixed 1000: `refused: unfunded`. No ordinary member can run any bend program. | x1: `/ci/xp-log` outputs in this session; x2 `/ci/x2log/params.json` | (a) infra/ship (genesis params), (b) coordinator: envelope price in `activity_world.py` `policy_of` vs `deploy/door` `funding` | (a) yes: params + objectiveInvocation, world x2. (b) open: sponsor `provision` makes an account but not a member-usable reference (not pursued) |
| E2 | certification headroom | `say` 90 times in a row in a fresh scratch world: write 70 refused `tail-bound: head/height <= certified/height + L fails: head 257 certified 0 bound 256; certify (mini checkpoint) to resume`. `mini-health` already prints `remaining=70 (minimum healthy headroom 64)` before that. `mini checkpoint --action certify` then took 16.9 s at a 256-height tail and writes resumed. Measured write rate with three parallel members is 2.7/s (45 says in 16.7 s), one `story new` is 19 heights. On the demo the only thing between the world and a global write halt is `mini-certify.timer` (every minute). | transcript above; `mini-health` lines | infra (certifier cadence, a health alarm on `remaining`), kernel owner (is a hard global halt the intended behaviour at 4 writes/s for a minute) | yes: ran the certify by hand |
| E3 | story refusal does not name the clause | tale story, member 2: `go 3` from the anteroom without the key. `why` prints `failing the whole law: all [ ... ]  it reads no single slot of the request  no change to the request passes it`. The tale's own clause 4 is named "needs key (exit 1 -> 3)". README promises a refusal names the clause. | x1, member-2, attempt `move-602397988617` | kernel/refusal reasons (law-denied clause naming), shell `why` | n/a |
| E4 | guard refusal is raw and unhelpful | `invoke w2 notes write 2 9 1` where the field is 7: refused as `operation-rejected: ... Reject.scalar (...guardRejected 0)`; `why w2` says only `the operation was refused by its controller`; the outcome JSON prints `detail` and `phase` as hex strings. Stale-expected-value is the common case and `can notes` knows the passing write. | x1 member-4 | shell (`why`, outcome rendering) | n/a |
| E5 | web `/room` lists every reference as a room | alice `GET /room` on x1 web: lists `account`, `b1`, `m1`, `n4`, `name-open-...`, `tl.cast`, `den-2834922086` beside real rooms; `room list` in the shell lists only rooms | `/ci/xweb/body-alice.html` | web face (`resource-client` room page) | n/a |
| E6 | `pay status` / `pay address` without an argument | `pay status` -> `error: a reference name is 1..128 bytes ...`; `pay status account` works (`credit 888`). The grammar says ACCOUNT-REF is optional. | x1 member-1 | shell (`pay` default ref) | n/a |
| E7 | `apps-e2e.sh` first install is `no-grant` at the birth | `world-up.sh $C/bin $C/bin /ci/xw1` then `apps-e2e.sh /ci/xw1/WORLD.env OUT 0dp7n6...(Simple Todos) 7qvcjh...(Hacker Slides)` with `MINI_MARKET_CACHE` and `E2E_MINI` set: 11 rows pass through the funded member and the delegations, then `apps birth` is `refused: no-grant ... (phase prepare)` after the tool reservation succeeded; same with the harness of be4ef7510 and of integ/src 06665f05; the reservation is released. | `/ci/xe2e1`, `/ci/xe2e2` (`install-*.err`) | app-reds / app-market (is world-up or the harness stale against main) | no |
| E8 | `help guide` | `help guide` in a scratch world: `the friends' guide is not installed at /usr/local/lib/mini/FRIENDS.md` | x1 | infra (jworld-scratch does not install it); check the demo ships it | n/a |
| E9 | file inputs: bound not named | `doc append ID NAME @FILE` with a 20,001-byte file: `session input must be a bounded regular file` (a 4,097-byte file says `document text must be 1..4096 bytes`; a 200 KB `doc push` says `at most 65536 bytes`; a push over 64 lines names its 64-action limit). Only the first message omits its number. | x1 member-4 | shell input reader | n/a |
| E10 | story/room templates are slow | `story new tl --from tale` took 19.9 s (19 template lines, one submit each); `chat new` 3.0 s, `chat invite` 2.4 s, first `credit` 2.0 s; warm single writes 0.5 s | x1 | law 17 candidate: batch the template's lines into one proposal | n/a |
| E11 | restart | `restart.sh` 9.6 s wall; first signed read afterwards 8.0-8.6 s at height 160-190 | x1 | measure the replay against height (law 17) | n/a |


## Status after routing

E1: infra says the shipped world pins the policy (670 hex) and door funding 1,225,000 (confirmed: a forge test member holds 1,224,993). Closed for the demo. E2: `mini-certify.timer` active on the forge, `mini-alert` now alarms at remaining < 96. Closed. E5, E6, E9: fixed on origin/lane/app-reds 0c176891e (E6 not yet re-checked in x1). E8: not a defect (installed on demo-dry). E3, E4: no owner (Lean/Host rendering). E7: untaken. E10, E11 and certify: integrator perf queue. Scaling: first read after restart 8 s at head 190, 23.4 s at head 769 (O(n) in history); certify at a fixed 256 tail 16.9 / 32.2 / 12.2 s at heads 257 / ~512 / ~768 (noisy, no trend).

## Forge pass (demo-dry, be4ef7510 world, taken down by infra for a rebuild)

Test members dw-10302104 and dw-10302056 only, driven by `/root/explorer/dm USER 'verb'` (runuser plus the box's mini-shell-ssh; deleted with the world).

| id | repro | owner |
|---|---|---|
| F1 | Hosted accounts have passwd home `/var/lib/mini` (root 0755). Running `mini-shell-ssh` as `mini-s-NAME` with HOME as sshd would set it, any write (`credit`, `say`) fails `/var/lib/mini/.mini/consent-anchors: Permission denied`. With HOME set to the session home it works (my hotpatch in `dm`). NOT verified over a real sshd login: needs a real ssh member to confirm or clear. | infra |
| F2 | The lobby's first line says "Start with the document called welcome", but `doc show welcome` as a member fails `cannot read .../refs/welcome.json`; a stranger holds no `welcome` reference. | infra/seed, door |
| F3 | Under load average 10 (installs running): first `say` 12.5 s and 44.8 s, `tail -n 3` 11.4 s; warm `say` 2.0 s, `tail` 1.7 s (hbox is 0.5 s). | integrator perf |
| F1 status | fixed by infra (mini-shell-ssh puts consent anchors in the session home); confirmed in code, member `say` works | infra |
| F4 | `ask lobby ...` -> `there is no Hermes in lobby` (infra already knows; summon blocked). | infra |


## Rebuilt forge world (be4ef7510, fresh genesis), test members dw-10302208 and dw-10302219

| id | repro | owner |
|---|---|---|
| F5 | First action of an idle session is very slow: `credit` 37.8 s (with `signed read batch: the observed source changed before the plan landed; observing again (re-plan 1)`), first `say` 29.8 s; later `say` 2.1-2.3 s, `tail` 2.3 s with two app installs ingesting (load 4 to 7). Re-time on a quiet box. | infra, integrator perf |
| F2 | still open: member `doc show welcome` fails, public /doc/welcome is 200. | seed/door grants |
| F6 | `ask lobby hello` is admitted (`#10 unacknowledged`) but no reply arrives: `mini-grain-resident@9872001` is `failed`. Infra knows (resident exits while installs ingest; restart pending). | infra |

Held: tale story with two players on the forge (key gate refuses `take key`/`go 3` out of order, GM narration shown on `look`); `chat new/invite/join/say/tail` between two members (writes 2.0-2.4 s warm, `chat new` 13 s, `doc new` 6.2 s under load); public pages from outside (/ 2.0 s steady, /doc/welcome 1.6 s, /tour /verb /story 0.5-0.7 s, /apps 1.3 s, 404s 0.5 s). Probe artefact: curl to the public URL from inside demo-dry hangs, use an outside probe.


## hbox world x3 (be4ef7510, demo params + objectiveInvocation, funding 1,225,000)

Worlds x1, x2, xw1, xweb and the e2e workers are down (x1's down listed one survivor that had already exited). x3 is up: `/ci/xp-log/m3 MEMBER 'verb'`, down with `jworld-scratch.sh down /ci/x3/w`.

| id | repro | owner |
|---|---|---|
| G0 | E1 confirmed closed in a scratch world: with the policy pinned and funding 1,225,000, `bend publish` then `bend run tally` are admitted in under 1 s; one run costs 121,779 (10 runs fit the grant). A repeated identical `bend run` is refused with the exact-retry guard (`--again true`). | n/a |
| G1 | A second member publishing the identical `Tally.obend` (`bend publish tally @Tally.obend --entry tally`) is refused `conflict: transaction identity conflict (phase replay)`; the package is already on the chain, yet the member then runs it fine. The refusal should say the package is already published. | kernel/shell refusal rendering |
| G2 | `bend answer SLOT @file` by the decider with a wrong reply shape is refused `Refusal.responseType "reply"`; a non-decider is refused `notDecider` (good, by name). The decider message does not say what shape the slot wants. Await deadlines are heights (62 against a current 61): on a busy world the window can pass between `await` and `answer`. | shell/bend docs |


### Bend happy path, restart in flight, web pass (x3)

| id | repro | owner |
|---|---|---|
| G1, G2 | fixed on origin/lane/app-reds (hint text after the Host refusal); G2 does not name the slot's actual type (needs a Host query). | app-reds / Host |
| G3 | Happy path proven: the `Tally` reply type is `Reply{amount: Nat}`, so the decider answers with `{"reply":{"tag":"record","fields":[{"name":"amount","value":{"tag":"natural","value":"7"}}]}}`, then `bend deliver OBJECT TX` resumes it (`total=7`, version 2, a new await). BUT with the default purse a `bend deliver` is refused `Refusal.awaitsFunding 60886 63454`: the first leg runs and answers, the resume cannot be funded. `bend run ... --deposit 200000` resumes fine. A default `bend run` cannot finish one answer; the demo's "10 runs" grant therefore buys 10 first legs, not 10 tallies. | bend defaults (`activity_world.py` policy, `bend run` default deposit) |
| G4 | Two height scales: a run/answer/deliver receipt says height 86/87/88 while `bend await` in the same minute says height 96 and deadline 99 (about +10). The await window is `patience: 4`; on a busy world (two writers) `await` read height 78 against deadline 77 yet the answer was still admitted, so the printed heights are not the clock the deadline is judged in. Not shown too tight in practice, but unreadable. | shell `bend await` rendering |
| G5 | Store restart with a `bend answer` in flight: the in-flight call gets a clean `cannot connect`; the retry after the restart is admitted once; a third try is `conflict: transaction identity conflict (phase replay)` (same unhelpful wording as G1 for a double answer). Nothing doubled. | refusal wording, app-reds |
| G6 | Web as member (alice, bob over the dev helper): login 303, `/doc/new` 200 (8.7 s the first time), append 0.7 s, `/doc/webdoc` shows the text, `/bend` lists t1..t4 with their awaits, bob gets 404 for alice's doc (`no usable workspace reference`), anonymous `/doc/webdoc` 404. A re-posted append form appends again (no idempotency on a repeated form; two distinct proposals). `POST /verb/credit` without an alternative returns 400 `which alternative of the usage?`. | web (idempotent forms: decision) |


## Reshipped forge world (be4ef7510, fresh), test member dw-10310244

| id | observation | owner |
|---|---|---|
| H1 | F5 persists: the first signed read of a fresh session took 20.7 s (`credit`); the next `say` 1.3 s, `tail` 1.6 s; after an idle gap `say` 1.4 s and `credit` 1.5 s. Only the very first signed read of a new member is slow, which is the stranger's first minute. | infra/integrator perf |
| H2 | Public `/doc/welcome` answers 200 (1.7 s) on this world, against the handed-over "404" known red: stale or fixed. Member-side `doc show welcome` (F2) still fails, no `welcome` ref. | seed/door grants |
| H3 | `ask lobby ...` is admitted as a lobby turn ("said in lobby") and `hermes status lobby` prints only `#8 unacknowledged`; the member is never told why (`no-credential` is the cause, known). Whatever message ember's key decision ends up with, the asker needs a visible reason in the room. | Hermes dispatch (member-visible refusal) |
| H4 | `apps search` lists every app as `[unverified; not swept]` with `typed tools: declaration-unavailable`, and `apps list` fails `appsWorkerUnavailable` until the worker is up (known). Fine for the known red, but the unswept label on all 22 adopted packages will read as broken to a stranger. | app-reds |
| H5 | `reports -n 2` as the sender of a `feedback` report: `this session founded no feedback-NAME room`. The member who files feedback gets no way to read it back. | shell |
| Public | / 2.4 s, /doc/welcome 1.7 s, /apps 1.3 s, /doc 0.7 s, /receipts 0.7 s, /tour /verb /story /healthz 0.5-0.7 s, /join 503 (held). | n/a |


## Candidate 35737eac4 re-explored (hbox x4, funding 1,225,000, default purse)

| id | result |
|---|---|
| G1 | fixed: the second publish says `this package is already published: artifact ... package ...; bend run it`. |
| G3 | holds: a tally (run, answer, deliver) spends 152,223; after the deadline one more `bend deliver` ends it (phase none) and refunds 60,885, net about 91,338. Until that last deliver the purse stays locked (a user who never delivers keeps 60,885 tied up; the program does not end itself). 10 completed tallies fit the grant only if every one is finished that way (8 un-finished ones exhaust it). |
| G4 | fixed: receipts and `bend await` print one clock (run 57, await 58, answer 58, deliver 59, show 60). |
| G6 | fixed: a form POST with the page's `attempt` token twice gives admit then a replay (one append); the same token with other text gives 409 `Already submitted`. A POST without a token still appends a new proposal (expected). |
| H5 | fixed: `reports -n 3` as the filer shows the report with the build sha. |
| E7 (superseded below) | was: `world-up` plus `apps-e2e.sh` on 35737eac4 still fails the first install: `no-grant ... (phase prepare)` at the application birth (2/12 rows; evidence `/ci/xe2e4`, `/ci/x4log/a1.out` on hbox). Owner: app-reds / the volume-helper lane. |
| not re-tested | member `doc show welcome` (needs the door's tick; scratch world has no door). |


### E7 re-run on 35737eac4 with scripts and deploy from staging beedc5de4 (hbox world-up + apps-e2e)

| step | result |
|---|---|
| no-grant at the application birth | FIXED: the first install's tool reservation and birth are admitted (`birth admitted`), member spend 10,360 of 20,000; the delegation-cost fix works. |
| install with an unseeded cache | `undecided: package ... is not in the quarantine yet` (no market fetcher runs in the harness; harness input, not product). |
| install of the pinned EtherCalc from the shared cache | `packageIdMismatch`: the cached `ethercalc-<sha>.spk` hashes to 93bd2c29..., not the index's package id. Harness input. |
| install of Simple Todos after seeding the cache with the real download (`mini-market-fetch fetch`, sha256 prefix equals packageId) | RED: `appIdMismatch: Simple Todos 5830d701... was refused by this box's ingest`; verdict file `/ci/xe2e7/verdicts/5830d70137cdae158118884da8790870.json` = `{reason: appIdMismatch, signedAppId: "", verdict: refused}`. An empty signedAppId means the ingest never produced a signed app id (it did not fail on a mismatch); likely the ingest unit or signature check failing on this box. Not diagnosed further. Owner: app-reds (spk-ingest / the worker's ingest stage). |
| second app (Hacker Slides) in the same run | birth refused `resourceBatch` after the first install had spent 18,730 of 20,000: the harness's 20,000 funding covers one install. |


### Hotpatch spk-host from 5f5e99324 and a load pass (35737eac4)

| item | result |
|---|---|
| spk-host from 5f5e99324 | built on hbox in 1 min 8 s (`/ci/x4log/tgt/release/spk-host`), but two overlay attempts did not install it (read-only hard-linked copy; a failed script edit), so no live verdict; the integrator then superseded the commit (c730fd3ea) and asked to wait for the next cut. Worlds torn down by PID file. Harness lesson: overlaying one binary into a copy of `$C/bin` needs `rm -f` first, because the files are hard links with mode 555. |
| load: 4 members x 25 `say` + 10 doc append/submit at once | 100 of 100 says and 10 of 10 doc appends admitted, wall 33.5 s (3.3 writes/s), `say` mean 1.27 s and max 3.0 s, doc submit mean 0.91 s, no refusals; the room tail and `doc show` are complete and in order. |


### CONSENT-STORE "after" numbers (eca98bde7-resvar2) and batch 3 candidate a4cb65af

| measure | before (be4ef7510) | after (eca98bde7-resvar2; hbox load 6-10) |
|---|---|---|
| fresh member's first signed read | 20.7 s forge, ~2 s hbox | 0.79 s at height 202, 0.46 s at 803 |
| restart wall / first read after | 9.6 s, 8.0-8.6 s at h190; 26.0 s, 23.4 s at h769 | 5.1 s, 0.19-0.46 s at h803 (flat in height) |
| certify a 256 tail | 16.9 / 32.2 / 12.2 s | 0.8 s at 266, then 5.3-6.6 s to height 1100 |
| `story new --from tale` | 19.9 s | 27.7 and 46.3 s at low height, 41 s at about 1100 (not improved; per-submit cost, hot-path row 12 still open) |

Batch 3 (a4cb65af): `bend settle` works. After run, answer and deliver (spent 152,223), `bend settle` delivered the past-deadline tally (phase none, `total=7`) and refunded 60,885, net 91,338 per tally; a second `settle` and another member's `settle` say `0 delivered`. Apps (apps-e2e, world-up and harness from the candidate's own source.tar): the signed-identity fix works, so the install gets past ingest and create; NEW RED at START: `spk-host: grain refused: application has no route; grain route must bind at least one entrance` (evidence `/ci/xe2e10/install-0dp7...json`). Second install in the same run: birth refused `resourceBatch` because the harness funding of 20,000 covers one (`MEMBER_FUNDING=40000` is the knob). Hacker Slides' real download is refused upstream (`http-526`), so only Simple Todos could be seeded.


### Batch 3 multi-member pass and the route-before-START fix (hbox)

| item | result |
|---|---|
| web flows (a4cb65af) | `doc new`, append, re-POST (replay then 409 for other text), `/bend`, `/room` (rooms only), `/receipts`: all fine. H4 wording not checkable (scratch world has no market index). |
| restart mid-activity then `bend settle` | works: 2 tallies, one answered, restart between answer and deliver, settle delivered both past deadline (r1 total=7, r2 total=0), net 152,232 for the pair. |
| `reports` from two members | each filer sees their own report with the build sha; a non-filer sees nothing. |
| H3 hermes wording | untestable without a resident (scratch says `there is no Hermes in hroom`); needs the forge world. |
| apps with `mini` built from app-reds 6043dccd0 (route bound before START), `MEMBER_FUNDING=40000` | NEXT RED: install state `routing`: `the owner's route is not bound yet: .../mini query: refused: no-grant: this key holds no grant covering this target and operation (phase observation)`. The worker's route-binding step issues an observation query the member's key has no grant for. Evidence `/ci/xe2e11/install-0dp7...json`, `/ci/x4log/e2e11.out`. Owner: app-reds. |
| leaked processes | after `world-down.sh /ci/xw9` returned `removal_assertions=0`, five processes of the world were still running with parent 1 and no PID file (`mini codec-resident`, `minidregg-host ... codec`, `mini consent-resident`, `minidregg-client-consent`, `minidregg-link-sqlite-store serve`). world-down does not stop client-side residents spawned by the harness's workspaces. Not killed (no PID file); reported. The settings files these residents name still exist (`/ci/xw9/w/store/base/workroom/deployment/pinned-config.json`, `/ci/xe2e11/ws-controller/provisions/member9/observe/g0001/config.json`; `/ci/xw9` itself is still on disk), so demo-reds' self-exit (settings file or socket gone) does not apply and this is not a red for it. The red is that world-down leaves the world directory and its client residents behind. The integrator stopped all five by exact PID after reading their command lines (its COMMANDS.log); the world-down leak goes to dregg-infra. |


### Batch 6 (74e1cfa10) re-explore (hbox, load 9-15)

| item | result |
|---|---|
| refusal clause naming | PARTIAL. A stale-value guard refusal now names its clause: `why w2` prints `phase: prepare` and `clause: invocation preparation: declared-resource-controller: scalar: ... guard-rejected 0` (E4 improved; still not "your expected value 1 was stale, field is 9"). The story `go 3` out of order (E3) still prints `failing the whole law: all [...] ... reads no single slot ... no change passes it`; the tale's clause 4 "needs key" is NOT named. |
| warm latency | credit 211-256 ms; say 399-506 ms (b4: 650 ms / 1,100 ms). |
| warm `say` MINI_TRACE (client 272 ms total) | `mini workspace propose` 71 ms (host op144 1.3, op4 1.8, op5 11.5), `mini workspace submit` 200 ms of which host **op2 = 163 ms**, op1 22 ms. The client's own overhead is about 0 beyond those; 60% of a `say` is the Host's op2 (the admit/commit call). |
| doc-append growth, certify before each sample | 13 entries 1.0-1.1 s; 103 entries 2.1-2.4 s; 303 entries 3.4-3.8 s (b4: 1.8-2.2 / 3.8-4.1 / 6.0-6.3 s). Faster, still growing with history. |
| object create | 2.1 s then 1.3 s; `story new` 7.0 s (b5 14 s, b4 28-45 s). |
| apps-e2e, two installs, 40,000 funding | Simple Todos: past ingest, create, route; START now fails `spk-host: grain refused: UNRESOLVED: .../host/apps/<id>/g2 is uncertain (START attempted without a completion record); reconcile it before another START`. The harness retried START after a first attempt left no completion record; the first START's own failure is not visible in the install detail. Etherpad: birth admitted, download refused upstream (`http-526`), so nothing beyond fetching. Run took 1243 s. Owner: app-reds. |
| residents after teardown | the batch's resident pid files exist (`/ci/xa6w/w/a/c-*.pid`, `r-*.pid`), but after `world-down.sh /ci/xa6w` a `mini codec-resident` (3981220) and its `minidregg-host codec` (3981221) kept running 20+ minutes; neither pid appears in any pid file (the c-/r- files name dead pids), and their settings file under `/ci/xa6w` still exists, so self-exit does not fire. Left running, reported. |


### Batch 8 (dc61016cb): resident shell, concurrency, reads, resets (hbox scratch)

| id | result |
|---|---|
| I1 | Flaky world-up: `render-authorized-keys.sh` decides `mode=open` with `"$MINI" --help 2>&1 \| grep -qE '^[[:space:]]*mini shell'` under `set -o pipefail`. On the first attempt it concluded `mode=closed (the shipped client (dc61016cbbac) has no mini shell)`; the published copy's `--help` had exited 101 into the closed pipe (Rust panic on EPIPE), which pipefail turns into failure. It did not reproduce in 40 retries (20 per copy), and the second world-up passed, so it is a rare timing race. Two owners: infra (read the usage into a variable, then grep) and the `mini` CLI (a broken pipe on stdout must end quietly, not panic with 101). |
| I2 | Concurrent lines from ONE member: 16 parallel `say` over separate ssh connections gave 2 admitted and 14 refused, 9 of them `declared-resource-controller: stale-t...` and 5 `target ... moved since the plan was signed`. 16 parallel says from 4 members at once (4 each): 6 admitted, 10 refused. The resident shell does not serialize or retry a member's concurrent lines; a user with two terminals sees refusals for ordinary says. 16 parallel `credit` reads: all 16 fine in 302 ms total. Owner: perf-client (the mini-line resident) or hot-path (retry on moved target). |
| I3 | `mini` replaced mid-session (new inode moved over the path): the next three lines succeeded in 91-272 ms. |
| I4 | Reads no longer leave an attempt tree: `credit` x3 left `attempts/` at 47 entries before and after; `read-journal.tsv` exists. `history` takes 16 ms, `history all` 15 ms (48 lines). Good. |
| I5 | No resets: a 120-write mixed burst across three members printed no failure lines, no `reset`, no `broken pipe`. (H1b is Hermes-only; not reproducible here.) |
| I6 | Timings (multiplexed ssh, b8, height 250): plain ssh `help` 165-171 ms vs 11 ms multiplexed; `credit` 20-57 ms; `say` 94-231 ms (first 231); `tail` 133-138; `doc new` 1.0 s; `chat new` 2.6 s; `create` 0.8 s; `story new` 5.6 s; certify 5.9 s at height 250. Not different from b7 for writes. |

## Exercised and held

Three members in one chat room (`chat new/invite/join/enter`, 45 concurrent says all admitted,
founder-only topic and pin, reactions, an uninvited member cannot enter); a tale story with GM and
two players (the key gate refuses `go 3`, `take key` then admits it, each player has their own
cell); delegate, import, write, revoke (the grantee's next read is refused `revoked`); lost reply
(`submit --lose-reply-once`, `lookup`, `retry` twice: the same receipt each time); the Store
restarted under a running writer (clients got a clean `cannot connect`, nothing half-written);
`export world`; the web login, `/story`, `/doc`, `/apps`, `/receipts`, `/verb` pages for three
members; document limits are all named except E9.

## Not yet reached

Apps beyond the install attempt (E7), Hermes in a story or room (blocked on the forge), the public reader over app-made documents, the door and enrol path on the
real stack.
