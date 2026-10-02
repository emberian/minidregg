# Actual Mini adapter for the stream-continuity journey

`ws-continuity-fixture.py` creates a **fresh, isolated** signed EtherCalc Store and
provides the snapshot/revocation/STOP hooks consumed by
`ws-continuity-journey.py`. It has not yet qualified a joined native candidate.
The static/adapter tests do not substitute for that run.

Run on persvati as the operator of an already configured **isolated** SPK broker.
The broker must authorize the supplied grains root, candidate binaries, operator,
UID pool and resident units. The script neither starts nor replaces the global
`/run/mini-spk-broker.sock` service. Coordinate that socket with the retained
browser fixture before running; no public or retained fixture should be changed.
No provider is invoked. No source or native build is performed.

Create a private input JSON with explicit immutable pins (illustrative paths):

```json
{
  "root": "/var/lib/minidregg/spk/fixtures/continuity-common-UNIQUE",
  "manifest": "/home/ember/build/codex-world/bin-COMMIT/manifest.json",
  "expectedSourceCommit": "FULL_JOINED_SOURCE_COMMIT",
  "spk": "/home/ember/workbox/packages/ethercalc.spk",
  "spkSha256": "EXACT_SIGNED_PACKAGE_SHA256",
  "grainsRoot": "/var/lib/minidregg/grains/continuity-isolated",
  "appPrefix": "46",
  "leaseSeconds": 120,
  "enableHotRegrant": false
}
```

The manifest must supply `host`, `mini`, `store`, `verifier`, `spkHost` and their
`sha256` entries, all in one standard-named candidate bin directory. Missing SPK
artifacts fail before a Store is created. It must include stream renewal and the
current joined lifecycle/enrollment family. Supply an immutable manifest path;
the mutable `bin/manifest.json` is only a discovery pointer. Every hook rechecks
the retained artifact hashes. Fixture/package/script pins and exact subprocess
arguments, stdout, stderr and exit outcomes remain under the new private root.

```sh
python3 scripts/spk-platform/ws-continuity-fixture.py prepare /private/input.json
python3 scripts/spk-platform/ws-continuity-journey.py \
  /var/lib/minidregg/spk/fixtures/continuity-common-UNIQUE/journey.json \
  --output /var/lib/minidregg/spk/fixtures/continuity-common-UNIQUE/journey-result.json
```

The service phase starts one private `mini serve-operator` with the pinned Host
and config, then `mini serve-public-proxy` with that same config and the private
socket as its upstream. It never opens a second native Host over the Store. The
following workroom phase uses actual signed reads through the proxy; socket
existence alone is not source qualification.

The profile phase consumes the actual `spk-host grain init-store` result and emits
`evidence/profile-result.json`, naming the exact profile path and native state
root. Neither script derives Store identity from a config hash or scans for a
likely directory. The adapter binds that retained result to the initialization
result, config bytes, grains root and candidate binary pins before installation,
and checks it again on every hook. Deployment-specific identities therefore
remain the native host/broker's decision. A mismatched or noncanonical path fails
without overwriting another profile.

The existing `grain-store.sh` constructs the ordinary workroom genesis, including
controller 7, app owner/tool 8 and member 9. The adapter uses source-authored
session births for **participant 7 and participant 9**, delegates separate app and
package observation capabilities, issues separate owner-8 signed tickets and
delegates their separate ticket observation capabilities. Each route request explicitly
selects that participant's delegated `manifestObserveCapability`; the old owner
selector would not authorize principals 7 or 9. The route builder preserves the
legacy owner default when this field is omitted, validates canonical decimals and
refuses changing the selector on an existing immutable route. This selector grants
nothing: current signed Mini admission remains decisive. Both routes are created
before START, because the resident snapshots entrances at START. It then enrolls
both sessions against that running generation. All writes preserve their native
attempt directories; uncertain writes are never retried automatically. Failed
preparation is retained and cannot be rerun over the same root.

`revokeA` is an **app-owner action**: subject 8 uses its ticket control capability
to revoke A's delegated ticket observation capability. It confirms the native
outcome, requires A's source query to refuse observation, and requires B's ticket
query to succeed before returning. It does not pretend that participant 7 closing
its own session is owner 8 revoking a share. B's ticket and route are independent.

`generationStop` calls the source-backed grain STOP workflow, requires no running
resident in status, a retained STOP receipt anchor and a fresh signed app read
showing stopped phase 2. It leaves the stopped app and all evidence in place.
Store participant/operator services remain running for subsequent inspection.
The adapter has no cleanup command that erases data or terminates a potentially unrelated
process from an old PID file.

By default the generated journey omits `regrantA`. With `enableHotRegrant:true`,
preparation requires the joined resident's typed control socket. The hook closes
A's old session as its real participant owner 7, issues a fresh owner-8 ticket and
observation grant, enrolls that same session against the same app generation, and
creates an immutable replacement route. It then calls
`spk-host grain register-route --socket ... --request ...` with exact source-current
app/session generations and custody hashes. The new cookie/endpoint is returned to
the harness; the old route and revoked ticket remain intact. There is no app
restart. This optional path is **unqualified until its real joined journey passes**.

Every mutation hook creates an exclusive one-shot action marker before source
writes. An interrupted or failed hook cannot be rerun with fresh nonces. Its
retained native attempts must first be inspected for deliberate recovery.

## What the snapshot establishes

All app, session, ticket and payer reads go through signed `mini query` using the
actual native participant credentials. They must return the same source-verified
height and world root; a concurrent Store write fails the snapshot and retains the
evidence. A's revoked query must still fail while B's succeeds. Session active
state includes matching app, serving generation and active Web tag.

`storeHeight` comes from these source-verified challenge observations.
`dispatchCount` counts resident **committed-permit inspection journal files** for
the running generation. It is explicitly a physical journal observation, not an
independently exported source history event census. The full native Store audit is
run once at preparation, outside the timed renewal windows.

`billingCount` is null with an explicit explanation: this source has no exported
billing event census for the adapter. Payer balance is separately recorded from
an authenticated account query; it is not mislabeled an event count. Flat verified
Store height during a renewal-only window establishes no new Mini records,
including no billing writes. The direct billing-event counter remains unqualified.

## Joined replay, race, and seal regressions

The generated journey now includes `replayAcceptedA`. After owner revocation it
selects the earliest retained delivered A dispatch for the exact ticket, session
and generation, re-decodes its permit with the pinned Host, and submits its exact
retained signed ingress once through the private Mini v2 operator envelope.
It requires a receipt-only historical confirmation matching all four original
receipt coordinates, plus unchanged authenticated Store tip, payer balance and
physical dispatch inspection count. Request/reply frames, selection and decoded
outcomes remain in the private hook evidence. No returned permit is forwarded.
This establishes receipt-only replay/no new recorded delivery; it does not invent
an independent application delivery census.

Two input flags enable the additional native regressions:

```json
{
  "enableSameIngressRace": true,
  "enableSealRecovery": true,
  "sealSupervisor": {
    "brokerConfig": "/etc/mini-spk/isolated-fixture-broker.json",
    "brokerConfigSha256": "<exact reviewed SHA-256>"
  }
}
```

These supplement the existing preparation input, rather than replace its pins.
Race requires a distinct manifest with `spkHostFeatures:["integration-qualification"]`
and the exact feature-built `spkHost` hash. The native feature is not a public
endpoint or ordinary release bypass. The adapter reads the native next-operation
counter without changing it, writes the one-shot private trigger, and sends one
actual authenticated B page GET. It validates source-authored ready evidence
before writing go. Success requires one exact permit/receipt-only loser pair,
one authenticated accepted Store record, the normal resident's delivered journal,
the native app-response acknowledgement, and an actual HTTP 200 page response.
The loser's retained confirmation can be `installed`, `replayed`, or
`recoveredAfterUncertainResponse`; exact receipt equality and lack of another
permit matter. A direct classified billing-event count remains unavailable.
Unknown responses retain uncertainty and are never retried.

The race trigger is terminal for subsequent admissions in that generation.
Ordering is therefore replay, optional regrant/reconnect, race, optional seal
recovery, final STOP. Held B traffic continues during replay/regrant/race.

Seal recovery requires a previously unsealed B route. Existing valid A seals are
preserved. It creates an exclusive, explicitly labeled diagnostic collision at a
fresh seal nonce, invokes the actual registration consumer, and requires the
native publisher's retained pending record with exact admitted binding. It then
requires same-generation `resident-run` to fail at the retained-seal guard before
listeners appear. This invocation uses the original resident configuration and
its bound environment; it tests the native startup guard, not a full systemd
restart. The adapter performs native STOP, START to a newer source generation,
and fresh participant enrollment. Old seals and diagnostic bytes must remain
unchanged. The traffic harness verifies old streams ended, opens B in the new
generation, and checks its before-failure sheet marker and a fresh edit. Generation
transition evidence is explicit and is not mixed into same-generation continuity
counter comparisons.

The resident's OnFailure must be empty and Restart=no during this deliberate
fault. With `sealSupervisor`, the adapter invokes the narrow root helper via
`sudo -n /usr/bin/python3 ws-continuity-supervision.py`. It supplies the exact
fixture, app, source-generated unit, resident hash, root-owned broker config/hash,
and validates the root broker custody tag. The helper records prior policy,
creates only its own exclusive drop-in, and removes only that exact unchanged
file afterward—even if the fault test fails. Parent directories are synced;
interrupted install/restore is recoverable from the retained root record. Other
unit files/drop-ins are never edited. If the runner has already arranged this
isolated policy, omit `sealSupervisor`; the adapter still checks it. Ordinary
supervisor recovery remains a separate receiving case.

No joined native qualification has been claimed from these adapters. Local tests
exercise framing, refusal handling, exact receipt comparisons, one-shot behavior,
interrupted override cleanup and the traffic harness's lifecycle/persistence
checks. The actual run still requires a coherent pinned joined Mini/Host/SPK
candidate, signed EtherCalc package and root-coordinated isolated broker/unit
setup; it must not reuse a public or retained live fixture.

## Isolated candidate capsule and root driver

`brokerSocket` is an explicit fixture input. A nonlegacy endpoint must be exactly
`grainsRoot/broker.sock`; preparation passes the native `grain init-store
GRAINS_ROOT CONFIG --broker-socket PATH` argument and retains the exact returned
endpoint in its profile/result. Snapshot and root override helpers refuse a
changed endpoint. There is no native environment fallback. `delegateHosts` can
pin distinct browser origins from the initial immutable route; e.g.
`a.localhost:18447` and `b.localhost:18448`. Different ports on the same hostname
would still share browser cookie scope.

`ws-continuity-launch.py` is the root orchestration layer. It requires a root-owned
setup plan and the complete joined candidate manifest, including `browserProxy`
(`spk-browser-proxy`) and its hash. It stages a new root-owned capsule containing
exact binary copies and tracked scripts archived from the original manifest's
full `sourceCommit`. The original manifest is retained unchanged; staged paths
and script hashes are recorded separately. It rejects missing features/artifacts,
changed hashes, source symlinks and existing capsule destinations. No compiler runs.

```sh
sudo python3 ws-continuity-launch.py materialize SETUP_PLAN.json CANDIDATE_MANIFEST.json --expected-source FULL_COMMIT
sudo python3 ws-continuity-launch.py run /absolute/candidate-COMMIT/ready.json
```

The driver uses the same pinned `spk-host broker-serve CONFIG` image. It starts
only previously absent isolated service names, runs Mini preparation and traffic
as the staged nologin operator, and installs/restores the exact old-generation
supervision override as root. It grants no sudo privileges. The override request
is durably retained before installation. After an interrupted driver, this command
restores only that recorded fixture override using the helper's idempotent receipts:

```sh
sudo python3 ws-continuity-launch.py recover-supervision /absolute/candidate-COMMIT/ready.json
```

A second `run` never retries a partly executed journey. Inspect retained native
attempts to decide any further recovery. Command logs include monotonic start/end,
elapsed seconds, exit status and timeout uncertainty; fixture preparation phases
and every native hook command retain the same timing fields.

The staged journey performs STOP/new-generation recovery and keeps that new
incarnation running for the browser phase (`stopAfterJourney:false`). The driver
checks its actual, ordinary supervisor policy, then starts separate **loopback**
TLS proxies for the two current routes. Root checks exact fixture/app/Store pins
and non-symlink operator custody before using those paths; certificates and access
metadata are created with operator authority. `browser-access.json` is private and
contains only origin, certificate and token-file paths. Credentials are never
included in command output or public documentation. SSH forwarding and trust for
these exact private certificates are part of the subsequent browser setup.

Passing native traffic is reported separately from the still-required actual
browser edit, sharing/access change and persistence checks. Existing browser ports,
units, Stores, packages and custody remain intact.
