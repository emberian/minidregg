# Explorer findings

Present-state table, rewritten whole at each batch. Lane `lane/explorer`. Subject: candidate
be4ef7510 (hbox `/home/hbox/lanes/integ/candidates/be4ef751074ca28c7d306c2f2bcf61cda03893c8`),
explored as test members only. Batch 2, 2026-10-30.

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
| F4 | `ask lobby ...` -> `there is no Hermes in lobby` (infra already knows; summon blocked). | infra |

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
