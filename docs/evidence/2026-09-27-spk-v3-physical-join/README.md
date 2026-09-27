# Launch-bound physical consumer prerequisites — 2026-09-27

This cut adds no lifecycle admission or app launch. The `mini-spk-resident-install-v2`
config now requires a protected `qualify-launch` result path and fixed
`deploymentId`/`hostId` expectations. The historical v1 INSTALL config remains
accepted only without those v2 fields. V2 INSTALL still returns `Unsupported`
before a Mini request or image materialization because event23–25 Host routes
and fresh native callbacks are not yet source-qualified.

The v2 descriptor join checks the qualifier's raw signed-SPK SHA, embedded v1
package root, v2 launch root, canonical launch SHA-256, create-action count and
ordered digests, and continue digest against a new Mini-authored descriptor
from the same signature-verified SPK parse. `SourceBoundLaunch` holds that
package and descriptor together. Its START create selector accepts only the
source-inspected action index and digest, and never chooses a default action or
the signed continue command. Actual START remains guarded at the entry to
`resident_service::run`. The deployment/host fields are protected operator
expectations, not root attestation; the later root-owned volume witness must
match both plus Mini's exact 32-byte source volume ID before physical START.

| Source file | SHA-256 |
| --- | --- |
| `native/spk-host/src/install_service.rs` | `b6096b0dc65d7fea4973e5d744001f97fe9a81f87f882edab12db57eed26a5ef` |
| `native/spk-host/src/install_v3.rs` | `3ee97f791f24401a62aaa76b15d881ac7e277d2bee067384f9643e7942778603` |
| `native/spk-host/src/resident_launch.rs` | `e9fabfcad7bbaeb4ab6ee9cc80e77e671c07e380f5e6009845c6516fcfb84cae` |

An isolated hbox copy under `/tank/dregg-build/mini-spk-v3-agent/native`
matched these three source hashes. It used offline locked dependencies, two
Cargo jobs, and a `systemd-run --user` scope with `MemoryMax=4G`,
`CPUQuota=200%`, and `TasksMax=128`. Focused library nextest passed 5/5,
including qualifier equality, action selection, versioned identity pins and
attempt namespace refusal. Strict all-target Clippy passed. Neither check
opened a Mini Store or ran an SPK child.

| Evidence | SHA-256 |
| --- | --- |
| `focused-final.log` | `d96691f40f21835e94ccc46af3bea08782b7f13a93983c2bc0787ac63e2b4349` |
| `clippy-final.log` | `8b1f9b8b7266e108ebc38653c94ab29e08541572ee236da36c0142ac111c3b28` |

The source draft for op66/67 plans a current-image INSTALL or first-create
START request with a client correlation ID, full v2 descriptor, and optional
create index. Mini derives the signed operation ID, package root, selected
command digest and LE32 source volume ID before signature headers. Its Host
wire, op68–71 claim/completion paths, event23–25 callbacks and inspectors
remain outstanding. Continue selection requires a later Verified prior-create
certificate. No v1 package-root or old completion fallback may open START.
