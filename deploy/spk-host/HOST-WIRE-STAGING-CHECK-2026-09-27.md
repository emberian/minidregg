# Host wire staging check — 2026-09-27

This checkpoint changes only the physical SPK host. It does not enable the
`begin` or `dispatch` endpoint operations. Mini lifecycle claim op26/27 and
the current dispatch projection are still source work; no generic receipt or
caller JSON was treated as a permit.

Exact source SHA-256 values:

| File | SHA-256 |
| --- | --- |
| `native/spk-host/src/rpc_adapter.rs` | `19aa24b2db599b1325c3466e16163b2c98c3bd21ecd6b024435540f0c4d48a2a` |
| `native/spk-host/src/endpoint.rs` | `ba8f19511eed9cbf3a987dee60d7b322df9afd1c3cb972e60a82025ec3708036` |
| `native/spk-host/src/hostd.rs` | `a8384e558d34d4e3da8a35632e59721fafa2884f005b33d3d47f8c5f7605853c` |
| `deploy/spk-host/MINI-CLAIM-DISPATCH-CONTRACT.md` | `f5420c3a0bafff4de9465be47c829d824a9ae102027cb7cfd1f05a78be936956` |

The changes remove host-only nonzero checks on Mini `Nat` app/session/subject
coordinates, while `hostd` still requires positive process generation because
the source-owned BEGIN transition increments it. The fd 3 session cache now
has a fixed 32-entry limit with least-recently-used eviction rather than a
permanent capacity refusal. The focused test checks eviction selection; it
does **not** prove actual 33-session Cap'n Proto behavior. Cached sessions
still require an identical source fingerprint and every app-visible parameter
to be reused.

In a private persvati source copy, `CARGO_BUILD_JOBS=2 cargo nextest run
--locked --lib` passed 22/22, including the existing physical systemd/spawn
tests and the new zero-coordinate/eviction-selection checks. `CARGO_BUILD_JOBS=2
cargo clippy --locked --all-targets -- -D warnings` passed. The source copy's
three Rust hashes matched the table above after the tests. `git diff --check`
passed locally. No app process, service, Store, public listener, or paid
provider call was started for this check.
