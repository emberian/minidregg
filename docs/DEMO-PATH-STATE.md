# demo-path lane: state (2026-10-29, codex)

Lane `lane/demo-path`; starting tip `1fc05c9f6`. Work is prepared against local
`origin/main` `636b1baebb7d0b94a330cab6d5e6109f0c961f6b`. The sandbox refuses Git's
ORIG_HEAD lock, so the merge/commit/push is executable in `target/dp-commit.sh`:
it merges main first, applies the named patch, commits named paths and pushes.
The reviewed main-based source is in `target/dp-work`; the script carries this
state file too. No shared working tree was stashed or reset.

hbox evidence prefix: `/tank/lanes/demo-path/run-1029` (called **L** below).
Candidate: `/home/hbox/lanes/integ/candidates/f34b03095c5c440ddce4a1d1c1c875b05d792692`,
still the newest READY when rechecked at 17:09 UTC. Run roots are short `/ci/dp-*`:
J0 succeeds there; `/tank/lanes/...` is too long for its Unix sockets.

## Web story

The READY candidate predates `0be1e5b4b`: its source and ancestry do not contain
the operations-room guard / `pre_of` fix. Untouched candidate run
`/ci/dp-t1029/steps/JWF/hook.out` demonstrated the old story failure. Applying
that commit to the candidate source and rebuilding `mini` under `swarm-build`
(private Cargo target, two jobs) supplied the missing fix; other roles stayed
at f34. Build evidence: `L/mini-build.log`.

The exact story block, initialization and login from JWF were rerun in a focused
scratch hook: `/ci/dp-s1029/steps/JWF/hook.out`, **13/13 PASS**. This includes
invite, invited page/front notice, wrong-recipient join refusal, joining,
joined page, north to the anteroom, and the second north refusal. The stricter
final refusal check is recorded below. Reproducer: `L/story.sh` and
`L/src/native/resource-client/journey.d/jweb-story-focus.sh`.

The earlier full run `/ci/dp-t1029f/steps/JWF/hook.out` was 70/73, not a green
full-tour claim. Its three named failures were story-move, grants-many and
can-bare; the latter explicitly reported the signed-read rate limit. Cold
public-reader consent/body restart and helper warm-at-start all passed.
JWF now retains each failed row's full HTML, so a uniform headline does not
lose the actual reason. The retained rerun `/ci/dp-u1029` reproduced the same
three failures; its
`story-move-failed.html` explicitly names `rate-limited`, retry in 21 seconds.
Its command transcript names a refused query-batch, which the headline alone
did not expose. Do not replay mutating commands merely to hide a rate refusal.

`SubjectRate.hostDefault` was documented as provisional until tour evidence.
It is now 1200 signed requests per subject per minute (20/s), with the same
window law and no new exemption. Existing explicit operator policies remain
pinned. `docs/PD-HOST-RATE-DESIGN.md` records the sizing decision. The candidate
Host accepts this policy through its existing configuration, so the live test
uses `{limit:1200, windowMs:60000}` in both genesis and pinned config; it does
not claim a rebuilt Host default. Full composed rerun `/ci/dp-v1029`: **73/73
PASS**, JWF elapsed 483.309 s (published, not a performance gate). The 61-grant
`can` returned its bounded partial-answer notice after 100 s, as designed.

The impossible-move row previously matched the theorem name in static tour
copy and could falsely pass on a rate refusal. It now requires `law-denied:`
in the actual command transcript and retains `story-refused.html`. The final
focused rerun `/ci/dp-z1029/steps/JWF/hook.out` passed **13/13** with this stricter
assertion. The retained page names the real player-law refusal; replaying a
rate-limited command is not how the row becomes green.

## Browsing: the tail, not a draining purse

`ApplicationDispatchPending.chargeOf` measures the exact ordinary intent plus
its four protected observations and ingress bytes. `ownerBudget` provides a
capability ceiling; route/enrollment `perRequestBytes` is a per-request constraint.
Neither is a countdown consumed by these GETs. The pending write updates the
session, not the member's purse. Each admitted dispatch does advance history.

Fresh SandMD world `/ci/dp-b1029r` passed 215/215 GETs. Continuing a fresh fixture
in `/ci/dp-d1029` reached GET 228's 403 after 227 successes. Retained resolution:
`L/apps-retained/6101/g2/dispatch-op-231/resolution.json` (no-record, original
`refused undisclosed`). The next app reservation retained the decisive clause
in `/ci/dp-d1029/w/evidence/k-app-reserve-attempt/outcome.json`:
`tail-bound`, `head 257 certified 0 bound 256`, with the explanation
`head/height <= certified/height + L` and instruction to certify.
The difference between 206 and 227 successful GETs is preceding setup turns.

Fix: `world-up.sh` now starts the standing world's operator certifier using the
existing `mini checkpoint` admission path, half-tail trigger and two-second
poll. Its private workspace and exact service/PID belong to that world;
`world-down.sh` stops the certifier before removing the Store. The tail bound
remains 256. GETs retain exact admission and retry semantics: HTTP GET is not
proof that an arbitrary packaged app performs no effects.

Live fixed world `/ci/dp-c1029`: **350/350 GET 200**, certification advanced
through heights 129, 259 and 387. `L/certified.log` and
`/ci/dp-c1029/certifier/operator.log` retain the evidence. The reusable
`route-browse-soak.sh` checks fresh dispatch head advancement and certification
across L, retaining failures without retry. Its live smoke `L/soak-smoke` passed
3/3 with head 412 -> 415. All shell changes pass `bash -n`.

Both ordinary and carried dispatch receivers now retain the structured
rejection in their internal `durable dispatch refused: ...` detail. The Host's
existing operator log can name `tailBound` rather than discard it. Public
undisclosed refusals stay uniform. `scripts/pipeline/lane-check` completed both
changed receiver files on hbox against refreshed imports, with no errors:
`L/lean-check.log`. The new SubjectRate default passed `swarm-build lake lean`
(`L/rate-lean.rc` = 0). A whole Host rebuild and the actual receiving-path log
check remain for integration; no candidate binary is claimed to contain those
Lean edits. dregg-build SSH authentication was unavailable in this session.

## OwnTracks: stored, but the package reads the wrong identity path

Package `7191aab6061704b4a51103e25be4c9c0` runs ot-recorder 0.6.9. Its launcher
creates `/var/store/last` and `/var/store/rec`. Its fork's `http.c field()`
overrides query u/d and user/device with `X-Sandstorm-Username`; X-Limit headers
do not control the identity. POST 200 `[]` is the friends response, not proof
of a failed store.

An exact-PID recorder trace (`L/ot.trace`) captured the valid routed JSON body
and `X-Sandstorm-Username: Grain%20owner`, then the recorder writing under
`last/grain-20owner/grain-20owner/`. Same-route `/api/0/last` uses the unsanitized
name and returns `[]`. A direct diagnostic read in that grain's network
namespace, with the normalized identity, returned the exact written timestamp.
The tracer was stopped by its recorded PID. Package/source evidence:
`L/app-sources.tar`, `L/apps-c-retained`, and the mnutt/owntracks-recorder fork.

The write recipe now requires the exact new timestamp and coordinates, retains
POST/GET bodies and names `owntracks-readback-absent`. Repair the packaged
recorder to use one stable, consistently normalized principal at write and
lookup; rebuild/sign/qualify that package. Do not change Mini's global member
display name or forge route identity to make this package pass.

## Hummingbird: transient readback and an obsolete runner

Package `9365130605f1998f3d4aea205d8768ae` (0.4.1), source retained in
`L/hummingbird-source.txt`. `tracker.js` matches `/^\/tracking_pixel/`, so both
`/tracking_pixel.gif` and the older `/tracking_pixel/t.gif` are accepted.
`hits.js` emits and resets the hit interval every 200 ms. The dashboard socket
must be open before sending the beacon, and receive its correlated URL hit.
It is not a durable record that a later independent GET can read.

The old `qualification-write-readback-absent` was the declaration validator's
pre-dispatch refusal. Current `apps/interfaces/hummingbird.json` expresses the
compound conversation and passes that gate. `featured-qualify.sh` still calls
the legacy Python row runner, whose Engine lacks `protocol: conversation`:
the live rerun (`L/apps-c-q/rows.tsv`, `L/hummingbird-current/result.json`) reached
`binding-protocol-unsupported` before app traffic, also with the existing
websocket-enabled venv. This is not a failed recorder write.

Use the existing native `mini app-interface --action qualify` / controller's
hidden `mini_app_<alias>_qualify` on the member's installed attachment, and
retain native dispatch receipts plus the correlated socket hit. That receiving
path remains to be run; do not add a second Python conversation interpreter.
See `docs/APP-INTERFACE-2026-10-28.md` and `native/mini-sdk/APP-INTERFACES.md`.

## Earlier work retained

- `8148992f6` / `658536adf`: concurrent story invite and log-directory fix;
  prior JSGM run on 2b8f75dcb passed 39/39.
- `27db3d1b7` on lane/demo-path-market / lane/spk-fresh remains held: fresh index,
  adoption and real featured-package resolution test. Revisit when Davros,
  DokuWiki and Hledger packages are built and the fresh index is regenerated.
- Earlier WordPress lifecycle/write evidence is unchanged. IPython run-a-cell
  and the separately owed japps rows were outside this run.

## Integration and cleanup

Every world started here is down. The four standing-world roots
`/ci/dp-b1029`, `/ci/dp-b1029r`, `/ci/dp-d1029`, `/ci/dp-c1029` each recorded
`removal_assertions=0`; journey cleanup ran for all six web roots. A final
audit found no live processes in those roots' retained PID files. The trace
process is also gone. No other lane's files, caches or processes were removed.

BATCH FOR THE PARENT: execute `target/dp-commit.sh` outside the metadata sandbox;
merge/integrate in dependency order and build the Host once on the designated
build host. Confirm a forced tail refusal names `tailBound` in the operator log
while the public reply stays undisclosed; run the native Hummingbird attachment
qualifier and carry the OwnTracks recorder normalization repair into a newly
signed package. These are receiving/package checks, not requests for a policy
decision from ember.
