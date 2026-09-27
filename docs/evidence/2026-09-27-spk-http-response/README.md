# Private SPK HTTP response component, 2026-09-27

This checkpoint prepares the physical WebSession-response-to-HTTP mapping for a future Mini-authorized SPK request. It is **not wired** to the private HTTP entrance: authenticated app requests still return 503. No candidate projection, historical receipt, or caller JSON authorizes an fd3 call. The native exact-CAS committed-permit route is pending.

Owned source files:

| File | SHA-256 |
| --- | --- |
| `native/spk-host/src/http_response.rs` | `98e37a8b337ed8c2d959ac8f38df3f023bede96c59a414d1776128a7b4eb9792` |
| `native/spk-host/src/http_entrance.rs` | `6b645fabd9c816ccc769a1137bd405b56f61c6fae7af9d3523431521ad362277` |
| `native/spk-host/src/lib.rs` | `ac21d6a7e1633869f4308e2f8db87306c49c6dd51c638e6ef69777ba772fc177` |

The response codec preserves binary Git bodies, suppresses a HEAD body while retaining its length, omits Content-Length for 204/304, bounds aggregate headers to the private TLS proxy's 64 KiB head limit, safely encodes UTF-8 download filenames, supports relative redirects and app cookies including absolute Unix expiry, and rejects an app attempt to replace the host session cookie or inject security/framing headers. The stale-socket doc comment now matches the existing flock, `ConnectionRefused`, and device/inode checks; its behavior did not change.

Linux verification used a private copy of `native/spk-host` and `native/spk-rpc` on hbox at `/tmp/mini-spk-http-response-20260927/native`. The source files above matched the copy byte-for-byte. To avoid persvati's full root filesystem, hbox compiled with two Cargo jobs and a private Cap'n Proto 1.1.0 compiler/schema copy; no app or Mini service ran. Commands from the private `native/spk-host` directory:

```sh
CARGO_BUILD_JOBS=2 cargo nextest run --offline --lib -E 'test(http_response)'
CARGO_BUILD_JOBS=2 cargo clippy --offline --all-targets -- -D warnings
```

Observed verdict: focused nextest **7/7 PASS** (30 unrelated library tests filtered); strict all-target Clippy **PASS**. The private compiler path and library path were set to `/tmp/mini-capnp-private-20260927/{bin,lib/x86_64-linux-gnu}` for both commands. `rustfmt` on the owned response file and `git diff --check` on the three owned files passed.

The shared `native/spk-host/Cargo.lock` SHA-256 was `c3d426d284e0b535b28826ce246a3d4e812a14615e6cfaf6f9e2ed29cf6eb9ed`; a local `--locked` metadata probe refused **before tests** because the current `native/spk-rpc/Cargo.toml` requires `serde_json` and the shared lockfile's `minidregg-spk-rpc` package entry omitted it. The private copy regenerated only its own lockfile, SHA-256 `feecc17aa41d4bb3812084df9397ea4af1e203f65e3a71ae3d06109746166e41`; the sole lockfile diff is addition of `"serde_json"` to that package's dependency list. The green Linux result is for this private resolved lock, **not** a shared `--locked` result. No shared lockfile was modified.

An initial separate persvati build hit ENOSPC before compiling this module. Its incomplete private target was removed; no retained fixture, Store, or historical target was changed. The hbox run above is the qualifying component result.

Root review subsequently applied the single missing `serde_json` dependency
entry to the shared lockfile. Its resulting SHA-256 is exactly the qualified
private lock hash `feecc17aa41d4bb3812084df9397ea4af1e203f65e3a71ae3d06109746166e41`.
Local `cargo metadata --locked --offline --no-deps --format-version 1` and
`git diff --check` passed. This aligns the committed dependency selection with
the hbox check; it is not a second Linux test run.
