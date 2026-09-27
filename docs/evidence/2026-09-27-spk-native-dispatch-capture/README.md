# Private Mini dispatch reply capture, 2026-09-27

This component decodes the outer Mini Host stdio reply for dispatch submit op34: a little-endian 32-bit length, opcode 34, then one bounded source-framed payload. It preserves the exact success or outcome payload bytes and refuses op35 historical lookup, a candidate-only tag, trailing bytes, truncation and length drift. It does **not** decode the nested Lean permit or establish authority. A caller could construct matching tag bytes; only an operator-owned Mini invocation followed by Mini's strict committed-permit inspector and byte-for-byte comparison of the retained payload can feed a future delivery adapter. The existing private browser/API entrance still returns 503.

| Source | SHA-256 |
| --- | --- |
| `native/spk-host/src/native_dispatch.rs` | `514d4669f8f2e2e28c80b953fa117eb26646c1404281c7a8bea41fec4632c348` |
| `native/spk-host/src/lib.rs` | `b183f6c61df00f99b5664d2f4a9921b0426b825380f61549c1ac548f483084e4` |

The bounded private hbox source copy at `/tmp/mini-spk-http-response-20260927/native/spk-host` ran offline with the shared lockfile, two Cargo jobs, and the private Cap'n Proto compiler/schema copy. Focused `cargo nextest run --offline --locked --lib -E 'test(native_dispatch)'` first passed **2/2**; the final combined `test(hostd) | test(native_dispatch)` rerun passed **17/17** after the exact Host-frame bound and journal Nat corrections. Strict `cargo clippy --offline --locked --all-targets -- -D warnings` passed. `rustfmt` on the new file and `git diff --check` passed. No Mini Store, SPK process, network listener or live hosted service was touched.

The native max frame is **12,102,760 bytes including opcode 34**; the parser rejects a length above that, and the journal captures at most 12,102,759 payload bytes. An oversized synthetic frame test covers this boundary. This correction followed the first 2/2 parser test and is covered by the final 17/17 result.

The op34 v1 payload is human-only for future physical delivery. Mini's agent-origin v1 projection lacks the checked parent budget/root; an agent-origin frame must remain refused until its separate source-owned v2 projection and parent-cgroup fence are qualified. The current parser classifies both only as opaque bytes and cannot trigger fd3.
