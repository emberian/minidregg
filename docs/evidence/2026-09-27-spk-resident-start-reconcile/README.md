# Resident START source and restart-reconciliation cut

Final source snapshot base HEAD at copy: `025bffa`. The private hbox source was
`/tank/dregg-build/mini-spk-v3-agent/native/spk-host`, using its isolated Cargo
target with two jobs. This cut did not call Mini, touch a Store, launch an app,
or stop a unit.

Source SHA-256 at test time:

| Source | SHA-256 |
| --- | --- |
| `resident_service.rs` | `6a592fb1c7feab39c63312baf24d8da8921f02912512f4692884c225f6394fdc` |
| `hostd.rs` | `4e4b807f7ca8f8252f515125548602cf893c3cbbd94f99999f3f75259c134189` |
| `lifecycle_v3_completion_native.rs` | `216c770a08e9fd7dd18a25bf3eeb1036635f674008ff9e96337f5624249d07f0` |
| `agent_api_lifetime_v3.rs` (concurrent pure matcher dependency) | `2a0b1053ff28f3203eaca67229261f1e150073391dce03a1c78d0c8f10faecf6` |

`cargo nextest run --locked --lib -E 'test(resident_service::tests::) | test(lifecycle_v3_completion_native::tests::) | test(hostd::tests::)'` passed 34/34 after the fresh START guard was removed. `cargo clippy --locked --all-targets -- -D warnings` passed. The final logs are `mini-spk-v3-start-callable-{nextest,clippy}.log`; earlier guarded-review logs are also retained here and hashed in `SHA256SUMS`.

The fresh `spk-host resident-start` path verifies the installed SPK/launch descriptor pair, protected volume
attestation, source-selected create or continue action, fresh BEGIN/claim,
physical one-shot launch, and V2 report/completion before transport bind.
On an occupied journal, it only reloads exact retained BEGIN/claim and source
inspection, recovers a submitted completion with read-only op39 if needed,
checks the saved completion receipt against original op38 or op39 source
inspection, and audits the prior unit. It never repeats the physical launch or
reattaches fd3. A live prior incarnation remains a required STOP and
source-authorized Continue workflow; this component cut does not claim that
workflow is callable. No native INSTALL/START fixture was run in this gate.
