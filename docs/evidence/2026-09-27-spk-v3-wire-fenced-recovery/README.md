# Versioned lifetime wire and fenced STOP recovery gate

Private hbox snapshot `/tank/dregg-build/mini-spk-v3-agent/native/spk-host`,
isolated target, two Cargo jobs. Source SHA-256:

| Source | SHA-256 |
| --- | --- |
| `hostd.rs` | `94b5b74e9c18ba5a596ac82c6f232c2e859d33d7be4f349e0a10fd1585f6d386` |
| `agent_api_lifetime_wire_v3.rs` | `38aa33ddf4c4c0a274c9e3c3d76e5a6f695230ce64f6189a9e519c03f` |
| `lib.rs` | `8a537ba144b106af7dc7dc0738dd3e46e60f76c66038208aa498cbf497af2f04` |

The focused Linux nextest slice passed 3/3; strict all-target Clippy passed.
The wire tests require finite v3 tags, exact binding hash field and no
caller-supplied current claims in forward dispatch. The hostd test proves the
new recovery-only path refuses a Running journal without calling the manager,
then permits exact Fenced recovery under the same lock with volume recheck.

This is a component gate only. No resident v3 listener, paid delivery, native
Store, or physical STOP was exercised. The `lifecycle_v3_stop_native` owner must
join its exact retained STOP marker to this recovery method before exposing a
callable recovery path.
