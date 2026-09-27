# Exact Fenced-only STOP recovery join

`lifecycle_v3_stop_native::resume_fenced_exact` is a separate recovery entry. It does not submit op26 or call the fresh Running fence. It reads the original owner-private STOP attempt's named Plan-v2, BEGIN ingress, claim ingress, op26 frame, committed-v3 frame, op26 requested marker and source-inspected committed JSON with `O_NOFOLLOW`, exact file ownership/mode/link count and bounds. The original op26 frame must contain the exact committed-v3 payload. The retained attempt hashes and four-field receipts must match the current pinned Host's read-only `inspect-stop-claim` output. The helper then checks the fsynced `stop-fence-requested.json` against those exact bytes and current source-selected event25 incarnation, checks the root volume witness, and calls only `Journal::resume_fenced_stop_manager_checked`.

The hostd recovery method requires **Fenced under the journal lock** before any manager command. Running and Stopped refuse. If the exact unit is already stopped, the under-lock audit retires Fenced without a second stop; if the same unit remains active after an uncertain stop, it rechecks the exact incarnation and volume and resumes that stop. A historical op27 receipt, a caller-supplied inspection JSON or a marker alone cannot fence Running. Each recovery invocation uses a fresh owner-private probe directory for its read-only current Host inspection.

The runnable supervisor call is `resume_fenced_exact(&operator, original_stop_attempt_dir, new_probe_dir, &journal, &volume) -> io::Result<UnitStopAudit>`. `original_stop_attempt_dir` is the same directory written by sealed `FreshStopClaim::submit_once` and `fence_exact`; the caller does not choose replacement ingress bytes or receipts. It must preserve this directory and use a new probe directory on each uncertain read-only inspection. The later STOP report adapter may consume the returned audit; there is no callable physical STOP CLI or integrated Store execution in this cut.

Source pins: `native/spk-host/src/lifecycle_v3_stop_native.rs` SHA-256 `652468c16fd4d5729ebcf6ef64ec2191f369f9ee409af84f2404288c1aca3ee9`; under-lock `native/spk-host/src/hostd.rs` SHA-256 `94b5b74e9c18ba5a596ac82c6f232c2e859d33d7be4f349e0a10fd1585f6d386`. The independently committed sealed `lifecycle_v3_stop_claim_native.rs` remains the only fresh physical entry.

The owned source and hostd hook were copied into the isolated hbox snapshot `/tank/dregg-build/mini-spk-v3-stop-agent` with its separate Cargo target. Bounded commands in that crate were:

```sh
CARGO_TARGET_DIR=/tank/dregg-build/mini-spk-v3-stop-agent/target CARGO_BUILD_JOBS=2 cargo nextest run --offline --locked --lib -E 'test(/stop_target_|stop_recovery_|resume_fenced/)'
CARGO_TARGET_DIR=/tank/dregg-build/mini-spk-v3-stop-agent/target CARGO_BUILD_JOBS=2 cargo nextest run --offline --locked --lib -E 'test(/source_bound_stop_checks_incarnation_and_volume_under_lock_and_recovers_fence/)'
CARGO_TARGET_DIR=/tank/dregg-build/mini-spk-v3-stop-agent/target CARGO_BUILD_JOBS=2 cargo clippy --offline --locked --all-targets -- -D warnings
```

Results: STOP target/recovery artifact tests 4/4 PASS, hostd checked-fence/recovery injected test 1/1 PASS, strict Clippy PASS; `rustfmt --edition 2021 --check` and `git diff --check` clean. Exact retained output is in `nextest.log`, `hostd-nextest.log` and `clippy.log`, pinned with source in `SHA256SUMS`. These are source and injected-component checks, not a real systemd/Store acceptance. The same-Store physical acceptance remains gated on a callable source-matched STOP supervisor and retained actual START/INSTALL evidence.
