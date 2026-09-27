# STOP physical target comparison, pre-fence component

`native/spk-host/src/lifecycle_v3_stop_native.rs` is a disjoint Linux module for the STOP physical target. Its private `StopTarget` is constructed from the read-only `inspect-stop-claim` output using the retained op66 STOP Plan-v2 bytes, fresh op26 committed-v3 frame bytes, original BEGIN ingress, and the retained four-field BEGIN/claim receipts. It requires the source inspector to echo those exact frames and receipts. It retains the verifier-selected event25 index, receipt, prior generation, unit, image, invocation ID, cgroup, canonical Custody, and physical volume witness. The comparison against a Running hostd journal and root volume witness requires exact app/generation/unit/image/incarnation/volume bytes. The pre-fence volume recheck is read-only.

This module has **no callable fence**. The physical STOP path still needs the hostd-owned audited under-lock fence that rechecks the same incarnation and returns typed StopAudit, plus caller wiring that accepts only the fresh op26 CAS-winner result. Neither a journal row nor the read-only `inspect-stop-claim` result alone authorizes a stop. No systemd or native Mini STOP was attempted.

The bounded Linux check used an independent source copy `/tank/dregg-build/mini-spk-v3-stop-agent` on hbox, copied from agent_api_host's private `mini-spk-v3-agent` snapshot with a separate reflinked Cargo target. Only that copy's `lib.rs` gained `#[cfg(target_os = "linux")] mod lifecycle_v3_stop_native;` for this compile. The shared `lib.rs` was not edited. The new file was copied from this repository at the SHA in `SHA256SUMS`. Commands:

```sh
CARGO_BUILD_JOBS=2 CARGO_TARGET_DIR=/tank/dregg-build/mini-spk-v3-stop-agent/target cargo nextest run --locked --manifest-path native/spk-host/Cargo.toml -p minidregg-spk-host -E 'test(/stop_target_/)'
CARGO_BUILD_JOBS=2 CARGO_TARGET_DIR=/tank/dregg-build/mini-spk-v3-stop-agent/target cargo clippy --locked --manifest-path native/spk-host/Cargo.toml -p minidregg-spk-host --all-targets -- -D warnings
```

Both commands exited 0. Nextest ran 2/2 focused tests; strict Clippy passed. The tests include receipt digest values larger than `u64::MAX`, malformed decimal refusal, exact frame/receipt equality, and prior invocation/cgroup/volume mismatch refusal. Only accepted indexes and counts are narrowed to the host's `u64` range; digest fields remain canonical decimal strings. The retained logs are `nextest.log` and `clippy.log`. This is component qualification against a private Linux snapshot, not a source-matched linked production artifact or an end-to-end STOP acceptance.
