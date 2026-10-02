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
