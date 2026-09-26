# Strict 8801 Hermes provider Linux build

Committed Mini source `8d88b9e` was copied into a private persvati snapshot at `/tmp/mini-hermes-provider-strict-8801-8d88b9e/src`. The snapshot contains only `native/hermes-test-provider/{Cargo.toml,Cargo.lock,src/}`. [Source hashes](source-sha256.txt) include `src/main.rs` SHA-256 `1e488dc50022bdbc3552ac811610a8c1f4df3b31ff68850a08acb25f2dea0d71`.

The immutable x86-64 Linux executable is `/tmp/mini-hermes-provider-strict-8801-8d88b9e/target/release/mini-hermes-test-provider`, SHA-256 `09e295b1691677580c63b943adf9cc95ec1a33527635bc6b579caba9f14c8400` ([hash](binary-sha256.txt)). The first `cargo build --release --locked` and `cargo nextest run --release --locked -j 2` were captured directly in [build.log](build.log) and [nextest.log](nextest.log): build PASS, 11/11 tests PASS. Both ran as isolated user transient units with `CPUQuota=200%`, `MemoryMax=4G`, `CARGO_BUILD_JOBS=2`, and a private `CARGO_TARGET_DIR`; peaks were 225.5 MiB and 117.9 MiB respectively, with no swap.

This is an executable handoff for mini_receiver's separate fresh 8801 receipt projection gate (`--content-receipt-8801`). It does not itself prove an actual Hermes prompt or publication receipt. The live hosted 7801/7803 controllers and provider services were not replaced or restarted.
