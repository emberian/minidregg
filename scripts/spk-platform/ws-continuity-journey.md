# Two-delegate stream continuity qualification

`ws-continuity-journey.py` drives actual EtherCalc Engine.IO v3 WebSockets through
**two distinct authenticated Mini entrances**. It is a traffic/evidence harness,
not a replacement for Mini admission or a fixture provisioner. The existing
`jspk10-ws.py` scenarios keep their original Unix/TLS defaults; the new `Endpoint`
argument allows separate origins, CA files, cookie files and Unix sockets in a
single process.

The common-candidate Mini journey is **not yet qualified by the local tests**.
Those tests use a small fake RFC6455/Socket.IO server to check the harness itself.
The checked kernel, resident, real packaged EtherCalc, source-backed snapshot
adapter, and actual owner revocation must be supplied for product evidence.

## Run

```sh
python3 scripts/spk-platform/ws-continuity-journey.py /private/fixture/config.json \
  --output /private/fixture/evidence/continuity.json
```

All credential, hook and evidence paths should be absolute. Hooks are explicit
argv arrays executed without a shell; this command authorizes their configured
actions. No hook is automatically retried, including after timeout or uncertain
results. Keep hooks and configuration private. Tokens are read from files and
sent only as `__Host-mini_spk_session` cookies; they are not placed in the report.
TLS verifies the supplied CA (or the system trust store when CA is omitted).

A configuration has this shape; replace the illustrative paths with the actual
fixture adapter and separately prepared member entrances:

```json
{
  "room": "continuity",
  "roomSuffix": "common-candidate-20261002",
  "leaseSeconds": 60,
  "durationSeconds": 135,
  "trafficIntervalSeconds": 2,
  "responseTimeoutSeconds": 10,
  "openTimeoutSeconds": 120,
  "hookTimeoutSeconds": 600,
  "cutoffToleranceSeconds": 2,
  "absenceObservationSeconds": 2,
  "delegates": {
    "a": {"subject": "7", "session": "6207", "endpoint": {
      "origin": "https://localhost:18443", "ca": "/private/a/tls.crt",
      "token": "/private/a/browser.token"}},
    "b": {"subject": "9", "session": "6209", "endpoint": {
      "unix_socket": "/private/b/http.sock", "host": "grain.test",
      "token": "/private/b/browser.token"}}
  },
  "hooks": {
    "snapshot": ["/absolute/path/to/fixture-hook", "snapshot"],
    "revokeA": ["/absolute/path/to/fixture-hook", "revoke-a"]
  }
}
```

The two subjects, sessions and token bytes must differ. `roomSuffix` must be a
fresh safe name of at least eight characters; an additional random suffix keeps
reruns from overwriting the previous test sheet. The exact room appears in the
report and in each hook's `SPK_CONTINUITY_ROOM` environment variable.
`SPK_CONTINUITY_ACTION` identifies the hook. No existing app data is deliberately
edited. Each initial open is an admitted dispatch; the subsequent edits/log
requests travel inside the already-open sockets.

## Snapshot hook

Print exactly one JSON object on stdout and exit zero. Diagnostics belong on
stderr or in an evidence file. Example:

```json
{
  "schema": "spk-ws-continuity-snapshot-v1",
  "app": "4501", "generation": "4",
  "storeHeight": 230, "dispatchCount": 2,
  "billingCount": null,
  "billingEvidence": "Source-verified Store height; direct billing event classification unavailable",
  "delegates": {
    "a": {"subject": "7", "session": "6207", "active": true},
    "b": {"subject": "9", "session": "6209", "active": true}
  },
  "evidence": ["/private/fixture/evidence/current-source-inspection.json"]
}
```

`storeHeight` must come from the source-verified current Store, not a count of
local files. `dispatchCount` is cumulative committed application dispatches for
the fixture; if obtained from resident committed inspections, label that scope
in the adapter evidence. `billingCount`, when available, is a cumulative count
of relevant verified billing events, **not a purse balance**. It may be null
only with an explicit `billingEvidence` explanation. A missing direct count is
reported as unqualified; unchanged source-verified Store height still establishes
that the renewal-only window added no Mini ledger records, including billing.
This says nothing about independent external payment systems.

`active` describes effective current session/grant authority, checked by the
source. A persisted `active` session alone is insufficient after its ticket or
observation capability is revoked. Snapshot must itself be read-only: no HTTP
GET through a paid/admitted entrance, no synthetic dispatch, no ledger mutation.
Extra provenance fields are permitted. Optional `evidence` paths must exist and
are retained in the report. The harness trusts the explicitly configured hook
for these observations; it does not reinterpret receipts or mint authority.

## Checked action hooks

`revokeA` must submit and confirm the real owner-authorized revocation, leaving
B's authority unchanged. Return only after its checked outcome is known:

```json
{
  "schema": "spk-ws-continuity-action-v1",
  "action": "revokeA", "confirmed": true,
  "artifact": "/private/fixture/evidence/checked-revoke-result.json"
}
```

The artifact must exist and must retain the actual source-checked operation and
its provenance. A CLI exit code or hand-written `confirmed` flag is not that
qualification. The harness also obtains a new snapshot showing A inactive and
B active. B continuously edits and reads its app log while the hook runs.

Optional `regrantA` uses the same action envelope. It must restore effective
current authority and any needed enrollment, with the **same running app and
generation**. It may return an `endpoint` object of the configuration shape if A
needs a new cookie or route. The harness then requires a new admitted A open,
an edit observed by B, and the old A stream remaining ended. A changed session
resource is not silently accepted; update the fixture design explicitly. If the
resident cannot add that new route while running, omit this hook and leave
regrant explicitly unqualified. Restarting the generation would break the B
continuity claim and is rejected by snapshot checks.

Optional `generationStop` must complete checked generation STOP and return the
same envelope with `action: "generationStop"`. After that confirmation every
held stream must end within the stated observation bound. Unlike revoke/regrant,
this hook is intended to end B, so the harness does not require B traffic during
it. Omitted optional hooks are explicitly marked unqualified.

## Evidence and limits

1. Open A and B and require exactly two new committed dispatches.
2. Exchange actual EtherCalc edits in both directions for more than two full
   configured lease intervals. Require unchanged Store, dispatch and available
   billing counters during this renewal-only window.
3. Perform checked A revocation while B continues fresh edits and app-log reads.
   Require A's reader to end no later than hook confirmation plus one lease and
   configured scheduling tolerance. The report records the actual time, including
   closure before a slow hook returns. This is an upper observation bound from
   confirmation, not a claim to know the precise commit timestamp.
4. After A ends, attempt a uniquely marked fresh A edit. A successful TCP write
   is not treated as admission. B must neither receive that marker in subsequent
   app messages nor find it in the app log; B must continue confirmed writes.
   This is a finite observation window, not a proof about indefinitely delayed
   app effects. Previously forwarded effects are not retroactively invalidated.
5. Require a new A open to receive an HTTP refusal (default 401/403/503, adjustable
   via `newOpenRefusalStatuses`), with no new committed dispatch or billing record.
   Record the actual status; 503 alone does not prove revoked authority without
   the checked revoke, current snapshot and continuing B evidence.
6. Execute optional regrant/STOP qualification if configured.

No flat-height claim spans revoke, grant, STOP, or explicit admitted opens. Their
snapshots are separate. Failures preserve partial structured evidence and exit
nonzero; they do not trigger retries, cleanup of the fixture, or further actions.
The harness closes only its own client sockets.

Run local harness tests with:

```sh
python3 scripts/spk-platform/test-ws-continuity-journey.py
```

They cover independent Unix credentials, verified localhost TLS origins using
the repository's public test certificate, sustained traffic, explicit missing
billing-counter provenance, optional regrant/STOP, refusal, failure to cut A,
extra dispatch/billing records, and a dishonest close-frame server that still
accepts fresh A writes. These are transport/harness tests, not Mini qualification.
