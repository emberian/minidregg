# Prequeue failure and shared-app release component check

2026-09-27. A private hbox snapshot of `native/spk-host` tested the exact
source below. No Mini Store, signed app, resident unit, controller, or public
listener was started. This qualifies a physical bookkeeping seam, not event21
admission or a real fd3 effect.

After controller `mark-send` and before `hostd.request_dispatch`, the resident
agent path obtains a noncloneable `PrequeueGuard` from its one `RpcDriver`.
The production `write_agent_delivery_marker` helper either writes the durable
marker and rechecks liveness, or consumes the guard's exact `NoEnqueue` fence
and records the operation as terminal uncertain. Once the guard is consumed by
`dispatch`, this prequeue abort is unavailable. There is no Drop release.

The focused A/B test uses a real `RpcDriver` over a Unix socketpair and the
production marker helper. It injects an existing `delivery-requested.json`
after A entered the host journal, refuses a mismatched identity fence, then
checks A's uncertain tombstone and replay refusal. Both the collided marker
and a retained route-native active marker remain byte-identical. Participant B
can subsequently request the same app's dispatch slot. This proves the
prequeue failure branch only; it does not prove a later queued worker effect
was absent.

| Source under `native/spk-host/src/` | SHA-256 |
| --- | --- |
| `rpc_adapter.rs` | `8329055ebfe767338281d3f37a180ff951be0c8ba0c812025bd644cff7d1fd7c` |
| `hostd.rs` | `15867f918cc455849aa28f482e50c68706e62b19203e9104c02f6da867758928` |
| `agent_api_server.rs` | `5f50dd105aec6e071279b76c49da8c04695b4432306cbfccff225182a2c49940` |

The isolated hbox source and local source hashes matched. Existing foreign
`sandbox.rs` (`8922016e35c4cebac6e91cc13c63a153b43a5f55c8e0694e6b37bd6c588af5e2`)
and `spawn_gate.rs` (`229a4581cff00f4ed3292936bb3a5f68c9eab374b4118e520c2e4d1df6c2603b`)
were present in the snapshot but are outside this change. The locked Cargo
file was `8fc4fc1a81c2ab4da2903c2a4095c620ec647fe7f131cb6176f23e5c1c6b86a3`.

The private `/tank/chreatures/mini-spk-resident-check-20260927` target used
`systemd-run --user` with `MemoryMax=4G`, `CPUQuota=200%`, `TasksMax=128`,
`RuntimeMaxSec=900`, two Cargo jobs, and `--locked`.

| Check | Result |
| --- | --- |
| `cargo nextest run --locked --lib -p minidregg-spk-host -E 'test(/agent_api\|prequeue\|worker_release/)'` | 22/22 passed, 84 skipped; unit exited 0, 144.7 MiB peak |
| `cargo clippy --locked --all-targets -p minidregg-spk-host -- -D warnings` | Passed; unit exited 0, 572.8 MiB peak |
| Local `rustfmt --check` and `git diff --check` on the three changed files | Passed |

[Nextest log](prequeue-r5.log) SHA-256
`09418a3969887a2cd5824e1d54031cf839f24daf40195d54ad097669fc5b94d6`;
[Clippy log](prequeue-clippy-r1.log) SHA-256
`7a235dabcf7df77a574b2dc429e2f0db6720bde32568463ad9592534ee7de535`.
The older shared-app component gate remains recorded separately; this check
does not qualify GitWeb START, Mini lifecycle v3, agent event21, or a
two-controller hard-EOF journey.
