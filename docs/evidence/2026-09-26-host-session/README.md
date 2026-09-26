# Persistent host replay rejection — initial 2026-09-26 checkpoint

This is a real native-host and SQLite-store run, not a mocked receiver. The
reusable driver is [`scripts/overnight-tests/replay-poison.sh`](../../../scripts/overnight-tests/replay-poison.sh)
with its Rust stdio probe. The private scratch run was
`/tmp/minidregg-replay-poison-initial-20260926`; only logs and hashes are here.
The scratch run contains a generated signing key and must remain private.

The host is the **initial** linked overnight snapshot, SHA-256
`edad4dad46dd1f7d0084ec881f046e281c2a134ebdadb8cf28843935b5933308`.
Its source basis is `d0cc5cdd1f2bbad0d033fd8a6d01d9e1397722a3` plus the six
paths and exact hashes in [`overlay-sha256.txt`](overlay-sha256.txt). The
builder's [`build-manifest.txt`](build-manifest.txt),
[`source-sha256.txt`](source-sha256.txt), and
[`source-verify.log`](source-verify.log) close the source-to-binary record:
591/591 compiled source hashes reverified. The full `Minidregg` umbrella,
`Host.Main:leanArts`, native link, and executable usage gates passed
([`build-gates.log`](build-gates.log), [`build-summary.log`](build-summary.log)).
This snapshot predates the canonical reply Message-ID parser fix, fn opcodes
12/13, V2 large-byte codec, and later AgentGrain/Host.Json runtime edits.

The existing native resource-client acceptance journey passed with this host
and the core Mini client SHA-256 `db2f0a75c86152f822fd76e6e921c5ae9de1b1f7368d4ccd688b6d5b9386d73f`.
It installed a birth at accepted count 1, a content change at count 2, and a
joint change at count 3. Its lost first content outcome was recovered through
exact retry of the retained signed call ([`acceptance.log`](acceptance.log)).
The driver captured the exact native images at those accepted states. Binary
and image hashes are in [`sha256.txt`](sha256.txt).

For rollback, a persistent stdio host opened the valid count-3 image and
answered its first `describe` frame. A separate native SQLite CAS installed
the previously accepted, valid count-1 image. The next `describe` received no
response; the host reported `verified history rolled back` at entry 1 and
exited with status 1. A later frame remained closed
([`rollback.log`](rollback.log)). A fresh host cold-opened the count-1 image,
showing that the replacement itself was valid.

For a same-height fork, the driver submitted a different content intent from
that count-1 parent. Mini confirmed the distinct count-2 fork as `installed`.
Fresh hosts cold-opened both fork and original count-2 images. The driver
restored the original through native CAS
([`restore-content-cas.log`](restore-content-cas.log)), then started a
persistent host on it. CAS installed the valid fork while that host remained
open. The next `describe` received no response; the host reported `verified
accepted-record prefix changed` at entry 2 and exited with status 1. A later
frame remained closed ([`same-height-fork.log`](same-height-fork.log)).

The result establishes persistent-process refusal of these two valid-image
rewrites for these exact binaries. It does not claim that a fresh host rejects
the old image or fork: cold opening both is part of the test. It does not
generalize to every history, storage backend, or later source snapshot.

A separate read-only [latency comparison](latency.log) used the same fixed fork
image and exact signed lookup call with a later Darwin poll-deadline-fixed Mini
client. Three cold direct retries took 8.92–9.00 seconds each; three retries
through one persistent socket host took 0.31–0.35 seconds each. All six binary
outcomes were byte-identical. The service startup was outside those timings.

An independent [Linux launch-fence race result](launch-gate-linux-race.log)
from persvati (see [platform](launch-gate-linux-platform.log) and
[source/binary hashes](launch-gate-linux-sha256.txt)) exercised the isolated
`launch-gate` prototype with a real transient systemd user service. A start
request was already in `activating/start-pre` when the gate was durably
fenced; its delayed ExecStart exited with status 1 and never ran the worker.
The probe also checked fence-before-init and fence plus exact unit kill for a
running worker. The [prototype contract](../../../scripts/overnight-tests/LAUNCH-GATE.md)
requires runtime and launcher integration; this result alone does not claim
that the current runtime uses the gate.

After the helper moved into `deploy/grain-host/launch-gate.rs`, the same
[race probe](launch-gate-linux-deployed-race.log) compiled that exact deployed
source and passed on persvati ([platform](launch-gate-linux-deployed-platform.log),
[source and binary hashes](launch-gate-linux-deployed-sha256.txt)). A real
transient user service was already in `activating/start-pre` when the durable
fence was written. Its delayed ExecStart refused with exit status 1 and no
worker ran. The probe also passed fence-before-init and running-worker
kill/cgroup-empty/retry refusal. The probe uses a harmless sleep worker; the
paired `bwrap` launcher and final native runtime require their own integrated
acceptance. This evidence is separate from the initial native host snapshot
above and does not retroactively change its source scope.
The deploy owner's separate
[`bwrap` integration smoke](../../../deploy/grain-host/GATE-INTEGRATION-2026-09-26.log)
exercised the matching launcher and helper on persvati, including the sibling
protocol check and exact-unit stop behavior. It is not a native Mini
reserve/worker/recovery acceptance run.
