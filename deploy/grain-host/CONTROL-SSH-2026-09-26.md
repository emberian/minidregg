# Linux SSH controller transport probe, 2026-09-26

This is a **component** probe of the actual Rust `grain-runtime connect`
binary over `ssh -T` to persvati, using `grain-ssh` and a transient user
systemd service running `probe_control.rs` against the exact runtime
`src/control.rs`. The helper supplies a control socket; it does not run a
Mini host, admit a task, reserve budget, start Hermes, or carry fn traffic.
The service and files were isolated in `/tmp/mini-grain-runtime-linux.IMMKgc`.

The runtime crate was copied as a standalone source snapshot and built on
persvati with `CARGO_BUILD_JOBS=2`. `cargo test --locked` passed both Linux
unit tests. Source SHA-256 values for the final probe:

| File | SHA-256 |
| --- | --- |
| `src/control.rs` | `6c8b41c29d0034cd8304bfc1e34f91af71cb10bca19318d81e0292f93153a0f1` |
| `src/main.rs` | `8a96c2ccc6caace7e42a7cca2a7ce74c0acf3208383349890cedfe17c978f848` |
| `src/mcp.rs` | `344b9afd1f38c95ecf949dbd0e30a7472f001d3bcddee4353755508575bc1dde` |
| `target/debug/grain-runtime` | `4c72772d506b3b96f3fe5b269f607a08b63705bd4536c777b66c33deb335b02e` |
| `probe_control.rs` | `7e147af213206f71489184005be308cf021f7b381d987f3fbff7fb675f225639` |

For each SSH connection, a Bash coprocess held stdin open. The client sent
`attach hard` or `attach soft`, read the attach line, sent `status`, read its
reply, and then the local SSH process received TERM to simulate abrupt shell
loss. The first hard attachment produced one `hard-interrupt:1` before
`detached:1:hard=true`. The following soft attachment detached with
`hard=false`, and a new soft SSH connection was admitted as attachment 3.
All six attach/status output lines were received before each disconnect.
The transient server unit ended inactive. Its unedited event log is
`CONTROL-SSH-2026-09-26.log` (SHA-256
`713d8c232d1014af85b99b2abf3d54e47f9275400109f6306b7ed96a1e3fe611`).

This establishes connector survival and attachment semantics across SSH
transport loss, including a soft reconnect. It does not establish a live
Mini generation fence or ongoing worker completion; that needs a bootstrapped
task, a current native host and a source-matched end-to-end run.
