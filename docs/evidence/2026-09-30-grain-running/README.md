# One grain running through the ordinary mechanism (2026-09-30)

The signed non-Git sntfy package (raw SHA-256 `bc424d5f…4f2d`, app ID `c6rk81r4…ddy0h`, version 18, signed
API prefix `/`) was installed, started, reached over HTTP, stopped and restarted on a **fresh Store** on
persvati, and a **second instance of the same package** ran beside it on the same host, all through
`spk-host grain` plus ordinary Mini client operations. Run root `/var/lib/minidregg/grains/m6-r4`, driven
by `scripts/spk-platform/grain-journey.sh all` as the transient unit `mini-grain-journey-m6-r4` (resumed
once as `mini-grain-journey-m6-r4c`, see below). Source: branch `m6-grain` at `a5bd4c0`.

## What each step is

- `store`: `grain-store.sh`: the reviewed workroom provisioner with the host lifecycle identity
  (`lifecycleManagement {8, 8008}`) and completion custodian key; no application.
- `birth-a`/`birth-b`: ordinary metered application births (`mini current-application-intent` + `mini submit`)
  owned by subject 8: A = app 9101 (package 9102, snapshot 9103), B = app 9201 (9202, 9203).
- `install-*`: **`spk-host grain install PROFILE APP_SOURCE APP_RECEIPT sntfy.spk`**: derives placement,
  custody, INSTALL config; runs INSTALL v3 BEGIN/claim, root ingest (once per package hash; B reuses A's image),
  completion, and root volume creation keyed by the Mini-derived volume ID.
- `share-*`: participant 8's session birth, event22 ticket (scope = the installed launch descriptor root),
  owner delegation of the ticket observe capability, then **`spk-host grain route`** (custodian + dispatch custody).
- `start-*`: **`spk-host grain start PROFILE APP`**: next generation and create/continue from retained receipts,
  root volume attestation, runtime system unit `mini-spk-a<app>-g<gen>.service` running `spk-host resident-run`.
- `enroll-*`: event28 session enrollment against the serving generation (after a restart: the owner closes the
  stale session, then renews).
- `get-*`/`post-*`/`poll-*`: curl over the route's Unix socket with its bearer token; each request is authored,
  signed and admitted by Mini (op36/37/34) before fd3 delivery to the app.
- `stop-*`: **`spk-host grain stop PROFILE APP`**: re-attests the volume, dispatches the existing source-authorized
  STOP (BEGIN, claim, physical fence, report, completion).

## Result (journey.log, seconds)

| step | exit | s | receipt |
|---|---|---|---|
| store / services / workroom / profile | 0 | 100.9 / 1.1 / 20.9 / 0.4 | |
| birth-a | 0 | 43.5 | app 9101 born |
| install-a | 0 | 120.0 | INSTALL completion record 17 (UID 993) |
| share-a | 0 | 249.5 | ticket 9120, issue index 20 |
| start-a | 0 | 111.6 | START (create) completion record 25, generation 2 |
| enroll-a | 0 | 64.8 | |
| get-a | 0 | 26.0 | `GET /v1/health` → 200 `{"healthy":true}` |
| post-a | 0 | 28.6 | `POST /m6grain` → 200, message `bHMSTsvnMFIu` |
| stop-a | 0 | 411.9 | STOP completion record 31 |
| start-a2 | 0 | 168.4 | START (continue, created index 24) record 34, generation 4 |
| enroll-a2 | 0 | 221.8 | session closed + renewed for generation 4 |
| get-a2 | 0 | 33.8 | 200 `{"healthy":true}` |
| poll-a2 | 0 | 43.9 | `GET /m6grain/json?poll=1&since=all` → 200, the same message `bHMSTsvnMFIu` published at generation 2 |
| birth-b | 0 | 140.0 | app 9201 born |
| install-b | 0 | 263.7 | INSTALL completion record 43 (UID 992; image shared) |
| share-b | 0 | 882.5 | ticket 9220 |
| start-b | 1, 1, 0 | 0.26, 0.25, 321.2 | refused twice before any Mini effect (see below); then START record 51, generation 2 |
| enroll-b | 0 | 166.4 | |
| get-b | 0 | 58.9 | 200 `{"healthy":true}` (both instances running at once: units a9101-g4 and a9201-g2) |
| status-a / status-b | 0 | 0.1 | A: g2 stopped, g4 running; B: g2 running |
| stop-b | 0 | 1492.3 | STOP completion record 56 |
| stop-a2 | 0 | 1638.3 | STOP completion record 59 |
| status-a2 / status-b2 | 0 | 0.1 | all generations stopped, units inactive |

Then `stop-services` stopped the Store's participant and operator units. No `mini-*` unit or app process
remained afterwards.

**start-b refused twice** with `runtime unit /run/systemd/system/mini-spk-a9201-g2.service differs from its
derivation`: a stopped runtime unit left by the earlier debug Store m6-r2 had the same (app, generation).
The derivation check refused before any Mini call; the stale m6-r2 units were removed and the remaining
phases resumed. Resident unit identity is Mini's `mini-spk-a<app>-g<gen>.service`, so one Store per host
is assumed.

## Files

`journey.log`; `steps/*.{cmd,exit,seconds}` per step, `steps/*.json` for every grain operation's output,
`steps/*.status` the HTTP status; `http/*.{headers,body}` the exact responses; `instances/<app>/` placement,
INSTALL completion, per-generation START completion and STOP receipt anchor, resident projection and route;
`grain-host-profile-projection.json` (seed paths removed); `inputs-sha256.txt` binaries/package/config;
`SHA256SUMS`. No key, seed, token or Store bytes are included.

Binaries: Host `minidregg-host-m6e` `f045a79e…73bc` (branch Lean, incremental builds from the e22d16b r3
baseline); `spk-host` `09ea24b8…5fb0` (branch Rust at `a5bd4c0`); client `mini-0007925` `3e9cb1ca…513d`;
helpers `ad03aede…193f`, `c8400412…892b`; bwrap 0.11.0 `7bbffeb1…12d5`.

## Caveat: the volumes were not fresh (RAN, found after the run)

The Store was fresh; the host's root volumes for apps 9101 and 9201 were not. The debug Store m6-r2 on the
same host created them (registrations dated 03:18 and 03:36; m6-r4 ran from 06:5x). Mini derives the volume
ID from (deployment domain, app) only, both Stores used the provisioner's fixed domain 8501 and the same app
IDs, and the root registration binds the host's deployment/host IDs but no Store identity. So `grain install`
verified and adopted the existing registrations (same volume ID `ad61fa4d…9afd` for 9201 in both), and B's
first START ran its create action on a `/var` where ntfy had already run. Nothing refused. The persistence
proof above is unaffected (message `bHMSTsvnMFIu` was published and polled within m6-r4). A per-deployment
unique domain (or binding the genesis identity into the volume ID or the root registration) is required
before two Stores may share a host.
