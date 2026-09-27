# Bounded SPK spawn gate component probe — 2026-09-27

This is a physical component check, not Mini lifecycle admission or an app launch. The public hostd endpoint still returns `unavailable` for BEGIN and dispatch. No SPK was executed; the only child executable in this probe was the pinned `/usr/bin/sleep` test fixture.

Source snapshot copied to Persvati under `/tmp/minidregg-gitweb-smoke-20260927/source/native/spk-host`:

| File | SHA-256 |
| --- | --- |
| `src/hostd.rs` | `900336ca706c9076cdbdc85c24ff67a1968dcf6b2a5c2ad5b4c526add4705789` |
| `src/lib.rs` | `ed03bef2bf1a0c1c95c2b532c3db160a922c647ae1d9ffed65ecfe86e8207886` |
| `src/spawn_gate.rs` | `05aca13dcd8d38dba040a275bbd4dfc76809f743830e354690fdbae4d1411917` |

The bounded Persvati `CARGO_BUILD_JOBS=2 cargo nextest run --locked --lib` passed 14/14. It includes a 10-second injected pre-exec hang: the parent timed out, killed and reaped the direct child, and did not release the journal lock with an unaccounted retry. A separate injected pre-exec exit shows that pipe EOF can race child death; a returned handle's first wait reports exit 42, and no readiness is inferred. `CARGO_BUILD_JOBS=2 cargo clippy --locked --lib --bin spk-hostd -- -D warnings` passed. The test executable SHA-256 was `af995ec442c238838fd9920beda0bafcba2c3f4a450637c722df7ac12d671a3a`.

A separate real system unit ran the root-only UID-drop test:

```text
sudo -n systemd-run --system --unit=mini-spk-gate-root-v2-20260927 \
  --wait --pipe --collect -p PrivateNetwork=yes -p NoNewPrivileges=yes \
  -p MemoryMax=256M -p TasksMax=16 -p RuntimeMaxSec=25 \
  -p KillMode=control-group -- TEST_ELF \
  --exact spawn_gate::tests::root_gate_drops_to_unprivileged_uid_before_exec --nocapture
```

`TEST_ELF` was the above source-matched test executable. The test opened and hashed the harmless executable, set supplementary groups empty, set real/effective/saved UID and GID to 65534, checked effective IDs, then executed it by its opened descriptor. The unit returned result `success`, `ExecMainStatus=0`, one test passed, runtime 1.405 s, memory peak 2.2 MiB. Subsequent `systemctl show` returned `ActiveState=inactive`, `MainPID=0`, and an empty `ControlGroup`.

The production gate requires a root-owned process, an exact SHA-pinned `bwrap` executable beneath protected ancestors, and explicit fd3/4/5 sources. The protected file path prevents app-UID mutation; the operator must keep its pinned inode unmodified during launch. It is internal to the future native-admitted lifecycle adapter; no socket request can select an executable. The gate holds the operation flock across durable `Entered`, bounded exec handshake, and durable `Running`; a handshake failure or uncertain stop never grants automatic rearm. EOF means no pre-exec error was reported, but it does not establish exec or app readiness. A separate liveness/readiness gate must precede serving. Exact unit invocation/cgroup cessation and Mini source-owned current claim projection remain required before an app BEGIN or request dispatch can be offered.
