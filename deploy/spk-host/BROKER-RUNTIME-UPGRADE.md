# Per-Store broker runtime adoption

A profile rebind changes the operator's pins. It does not change the root broker's
resident or supervisor executable. The upgrade sequence therefore has three typed
steps, all before admitting public traffic:

1. Bootstrap the new broker with the manifest-pinned target executable:
   `spk-host broker-serve ROOT_BROKER_CONFIG`. This is the existing root broker
   implementation and config contract, exposed through the already pinned image.
   The root upgrade controller owns quiescence, public drain and replacement of
   that broker process. No consumer silently restarts or edits its service unit.
2. As the Store operator, run `grain rebind-profile OLD_PROFILE ADMISSION` and
   retain the returned immutable successor profile.
3. Run `grain adopt-runtime PROFILE ADMISSION`, require the typed ready response,
   then START applications using that selected profile.

The broker's configured baseline executable and all previously pinned executable
paths must remain available. Adoption never rewrites the global broker config or
changes another Store's runtime. It stores a root-private per-Store record at
`GRAINS_ROOT/broker/runtimes/STORE.json`, renders exact supervisor **instance** units
for that Store, reloads systemd, and only then records `ready`. Interrupted render
or reload leaves `pending`; retrying the identical admission completes it. A
changed retry or a second upgrade while pending refuses. A ready retry returns the
retained supervisor set without modifying active units.

The response is:

```json
{
  "protocol": "mini-spk-runtime-adoption-v1",
  "brokerProtocol": "mini-spk-broker-runtime-v1",
  "store": "<Store key>",
  "state": "ready",
  "spkHost": "<target manifest path>",
  "spkHostSha256": "<target manifest hash>",
  "admission": "<root compatible-admission.json>",
  "admissionSha256": "<exact admission hash>",
  "supervisors": ["<exact source-rendered instance names>"]
}
```

The controller must compare these pins and the declared supervisor set; a command
exit alone is not adoption evidence. `grain runtime-status PROFILE` reports
`mini-spk-runtime-status-v1`, the same broker protocol and runtime fields, and a
state of `baseline`, `pending` or `ready`. This proves the typed protocol is served;
the deployment controller separately pins the actual broker process image.

Before changing runtime, the broker requires root-admitted original profile and
physical identity hashes, exact target image hashes, completed STOP records for
all retained generations, and stopped resident/supervisor processes with empty
cgroups and no queued systemd job. Unknown installed generations refuse. It does not execute the old Host
or infer a source history proof from the local root admission.

Every new resident installation carries its expected runtime hash. Legacy clients
may omit that field only for an untouched baseline Store. Per-generation root
runtime records prevent a historical unit from being started under a newly adopted
runtime. START checks profile/broker agreement before creating a generation, so a
missing adoption cannot strand a new never-begun journal. Package ingestion also
uses the Store's selected image. Pending adoption refuses launch, ingestion,
placement allocation and cgroup-class changes. Recovery verifies the app set still
exactly matches the set frozen in the pending root record before publishing ready.

`grain current-profile BASELINE` centralizes read-only discovery. Run it as the
Store operator with the original `STATE_ROOT/grain-host.json`; it performs no Host
execution and emits `{protocol:"mini-spk-current-profile-v1",store,profile,
profileSha256}` from the exact validated profile snapshot. Root controllers should
invoke it under the configured operator identity instead of parsing pointers.

This is source and Rust receiving-path coverage. A root-owned joined-candidate
upgrade, broker bootstrap, adoption, START and browser journey is still required
for deployment qualification.
