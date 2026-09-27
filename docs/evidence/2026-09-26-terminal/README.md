# Framed grain terminal source checkpoint

This checkpoint adds an opt-in presentation over the existing task control socket. It does not change Mini admission, authority, the raw `connect` protocol, or the admin socket. The new CLI is `grain-runtime terminal /absolute/control.sock [hard|soft]`, with hard as the default. `native/grain-runtime/TERMINAL.md` describes operator behavior.

## Source scope

| file | SHA-256 at review |
|---|---|
| `native/grain-runtime/src/main.rs` | `70315a196474b316a477f93a639653b1f20941f9bb9a5532fd8fb6509e0883e9` |
| `native/grain-runtime/src/control.rs` | `18da14149965e920d1332a205c8838b9400d61760180d2e1dcd0253923408ba8` |
| `native/grain-runtime/src/terminal.rs` | `bab9e5b5cb86a39080e8ec4d129daa260cc9eb319b60e25d66ae02dc383be1e2` |
| `native/grain-runtime/TERMINAL.md` | `99604bb9a818b090b7a8141ce3bb12d4774c934658dea782d9e18e4acf0b5156` |
| `native/grain-runtime/src/provider.rs` (test/contract comment only) | `531eb9adecc4b576e6cb54f33bd8029252c74d7c383c6aaa7f09f0a47fe8cddb` |

The source-owned control transport frames untrusted ACP text as JSONL `output` and controller state/completion as distinct events. The terminal prefixes model text on every displayed line and visibly escapes cursor, color, and bidirectional controls. Source status exposes a selected projection, not the private journal. The event pump retains each socket attachment ID and rejects a terminal command before Hermes dispatch if its claimed ID differs or the attachment is no longer current. Prompt completion additionally matches its request nonce. Bounded stdin lines, frames, and a 64-event local queue refuse overflow; stdin EOF shuts the socket write side directly so queue pressure cannot hide the existing hard/soft detach behavior.

## Checks and limits

- `cargo check --manifest-path native/grain-runtime/Cargo.toml`: PASS; current unrelated `resource_tools.rs` birth work emitted dead-code warnings because main wiring is pending.
- `cargo nextest run --manifest-path native/grain-runtime/Cargo.toml -E 'test(control::) | test(terminal::)'`: 9/9 PASS, including raw hard/soft EOF, framed output isolation, stale attachment, bounds, malformed frames, status projection, and terminal control-character rendering.
- `rustfmt --edition 2021 --check` on the three Rust files and `git diff --check`: PASS.
- Full crate nextest first stopped on `provider::tests::broken_local_reply_reports_failed_delivery_and_blocks_retry`: its test controller saw `local_write_success=true` despite setting client `SO_LINGER` to force RST before reply. That assertion depends on when the peer reset becomes visible to the gateway's small socket write. It then passed 10/10 isolated runs, and a second full crate run passed 50/50. With the provider owner’s exclusive edit window, this test became `client_reset_before_local_reply_never_retries_upstream`: it accepts either local write result, still requires the exact Delivery message, a controller-gated retry, and no second upstream delivery. `local_write_success` is explicitly documented as kernel write completion, not peer receipt. The corrected focused test passed, followed by full crate nextest 51/51. The earlier failure remains retained here because it exposed the inaccurate test contract.
- Strict all-target clippy currently stops on unrelated, unwired `resource_tools.rs` birth helpers and `cloned_ref_to_slice_refs` test warnings; there were no terminal or control clippy diagnostics.

This is a source/test checkpoint. It does not claim a live hosted terminal session or native publication acceptance through the terminal UI. Existing signed hosted workroom results used the raw connector.
