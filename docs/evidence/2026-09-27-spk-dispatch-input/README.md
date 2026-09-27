# SPK dispatch inspection and physical WebSession input

This is a component gate for the operator-private human dispatch path. It does
not launch an app, invoke Mini op34, or enable HTTP delivery. The private HTTP
entrance still returns 503. In particular, the JSON fixtures in the focused
tests are comparison fixtures, not native permits.

Exact local source SHA-256:

| file | SHA-256 |
| --- | --- |
| `native/spk-host/src/dispatch_inspection.rs` | `ff69d3d8a76150fbc20c9a67346501ecdcd0c905a2c3068828452b050d970d35` |
| `native/spk-host/src/dispatch_web_input.rs` | `b552a192e15e280db6d9d762332e31577684532521b7bb370af6acb3bb38bb94` |
| `native/spk-host/src/lib.rs` | `84bf0c502206e3492979dd17ae9c9228e13d6e9f077c77947c42da5dd5b3ecd4` |
| `native/spk-host/Cargo.lock` | `6a29cc886e300238f59cfb0b83b0530dbc769f5296697bfeef25656660e4f4c2` |

The lock change adds `sha2` to the already locked `spk-rpc` package entry. The
hbox private source copy included the committed BridgeConfig decoder from
`native/spk-rpc`; its `protocol.rs`, `web.rs`, `lib.rs`, and `bridge_config.rs`
SHA-256 values were `551376dcd58dd7d722bd026494a5999a0f82e0c9e41861217709827187b21acc`,
`ed777fe3e0ba6e80e62d0e108cc9d7a434672cc12e523f6e49bfa6046a95453f`,
`ad7f7626ded8465945942869ea9e7171c9454c1c0f656e125b9d1eb7eb4d58cf`,
and `15fbd3474f010d0e3d7a9a22949bf4f5a2b46ff150a381233d65ddcd463221fb`.
Only the two new host files, `lib.rs`, and this lock were changed by this gate.

On hbox, with a private Cap'n Proto compiler and `CARGO_BUILD_JOBS=2`, the
exact copied source passed:

```text
cargo nextest run --offline --locked --lib -E 'test(dispatch_inspection) | test(dispatch_web_input)'
7 passed, 47 skipped
cargo clippy --offline --locked --all-targets -- -D warnings
PASS
```

The component checks the byte-exact op34 payload echo from Mini's read-only
inspector, fixed participant selectors, human-only v1 origin, canonical
relative browser/API path, method/query/body/ordered headers, checked
principal/permissions/fingerprint and receipt agreement. The API path is
derived from the signed bridge prefix `/repo.git/`, never from a caller header.
The typed RPC mapping retains zero-length POST bodies without requiring a
Content-Type and refuses unsupported headers or wire values before fd3.

The joined private Host op36/37/34 signer, lifecycle claim v2/SPK descriptor
gate, systemd instance check, fd3 RPC, and HTTP response path remain to be
qualified together. Native op34 commit is point-in-time; a timeout or closed
fd3 response must retain the one-shot physical uncertainty tombstone and must
not resubmit the request.
