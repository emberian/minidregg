# Mini consumer Host-image pin: copied refusal and live lookup

Client source commit `99ca8c7` adds a version-two socket envelope carrying
the worker's expected Host executable SHA-256. The broker compares that pin
and the exact config bytes before forwarding a request. The upgraded worker
does not fall back to version one. The source-owned test run was reported by
the client owner as 33/33 Rust tests and `clippy -D` passing; no standalone
test log was retained, so the physical observations below are the durable
evidence for this specific gate. The client binary used here was SHA-256
`e0a492f9729fcbcb47ce20fe63a73e59d7092172bb8c4f47c0786ec4453c0263`.

In the **private copied B fixture** at `/tmp/mini-b-image-gate-20260926`, the
new broker served the old Lean Host image `919c3b7b…` while the migrated
worker expected image `49e8e6f0…`. The configured, service-pinned, and
retained-attempt config bytes all had SHA-256 `2d0072dd…`, so this was not a
config-pin mismatch. The migration was scoped to one already confirmed
retained call, SHA-256 `4ceab566…`, and made a read-only exact lookup; it did
not authorize a new submit or fn ACK. The broker refused the worker's
version-two request with `socket rejected request: host image pin mismatch`.
The worker entered `Held` at serial two. No new `retry-0001.bin` or
`retry-0001.json` appeared in the pending attempt, and no ACK attempt
directory appeared. The copied Store's post-gate SQLite SHA-256 was
`00a30179…`; the client owner also compared the copied Store directory
byte-for-byte before and after the test with `diff -qr` and reported no
change. That before/after equality is owner-reported, while the post-gate
hash is captured here. The old and new Host image values, migration receipt,
transport pin, refusal, and read-only known lookup are selected in
[`copied-gate-selected.json`](copied-gate-selected.json).

In the separate **live B migration**, the client owner stopped the old
service/worker, authorized the same retained call under the new Host image,
and restarted with the matching image. The migration config SHA-256 was
`c54ce20f…`, distinct from the copied fixture, while the retained call was
again SHA-256 `4ceab566…`. The first upgraded-worker lookup returned
`confirmed`/`replayed`, accepted count three, and matched the migration's
original transaction ID, event ID, image boundary, and accepted count. The
retained 132-byte lookup payload SHA-256 was `39e04ff6…`, also equal to the
copied fixture's read-only known outcome. This proves recovery of that
historical Mini receipt, not a new submit or an fn ACK.

The first live ACK attempt then returned a **different** typed refusal,
phase `fn-session` (hex `666e2d73657373696f6e`), after source-owned fn
cursor inspection failed. A separate bounded bridge probe with unset
`FN_B3_IMAGE` had zero stdout and stderr
`FN_B3_IMAGE must name the frozen fn image`; the client owner identified
that omitted launch variable as the cause. No immutable launch-environment
manifest was retained, so the cause is a diagnosed deployment condition,
not a proven env value inside the refused process. At the captured point the
worker was `Held` at serial three, and there was no successful `ack.json`.
The owner was implementing explicit ACK recovery. These selected records are
in [`live-migration-selected.json`](live-migration-selected.json). **This
evidence does not claim fn ACK success.**

[`sha256.txt`](sha256.txt) records the exact selected source, binary, config,
call, Store, migration, refusal, and probe hashes. Only bounded selected
JSON and hashes are archived here; no private key, full signed call, raw
Store, or live socket material is copied. The Host-image check is a local
deployment pin: the broker hashes the configured executable before spawning
it and relies on the operator keeping that path stable through launch. It
does not attest a malicious service owner or a remote fn image.
