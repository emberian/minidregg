# Corrected strict 8801 provider Linux build

Committed source `5ebaaff` was copied into a new private persvati snapshot at `/tmp/mini-hermes-provider-strict-8801-5ebaaff/src`. It contains only `native/hermes-test-provider/{Cargo.toml,Cargo.lock,src/}`; [source-sha256.txt](source-sha256.txt) records `src/main.rs` SHA-256 `3fc47aa90afc5f8ed1ca64447a28babc9027b030fadd49002cdb9c123bd7f916`.

This revision fixes the strict 8801 fixture's receipt check: a top-level signed query after tool disconnect can have a later image boundary than the historical publication. The fixture must project the four fields from the nested immediate `publicationReceipt`, while separately checking the signed query for the content view. The prior [8d88b9e build](../2026-09-26-hermes-provider-strict-8801-linux/README.md) and its logs remain unchanged; its ELF is superseded for a **fresh** receipt gate.

The corrected x86-64 Linux executable is `/tmp/mini-hermes-provider-strict-8801-5ebaaff/target/release/mini-hermes-test-provider`, SHA-256 `759cc0767cf193ee89ca41346e31aee9ce338ec33fc93aa8211e1e404d467d17` ([binary-sha256.txt](binary-sha256.txt)). Initial bounded `cargo build --release --locked` [PASS](build.log) and `cargo nextest run --release --locked -j 2` [11/11 PASS](nextest.log) ran with `CPUQuota=200%`, `MemoryMax=4G`, `CARGO_BUILD_JOBS=2`, and a private target directory. Peaks were 211.7 MiB and 112 MiB, no swap.

This is a source-qualified ELF handoff to mini_receiver for an isolated fresh 8801 actual Hermes MCP receipt test. It is not itself that acceptance result. No live 7801/7803 provider, controller, Mini host, or Store was changed.
