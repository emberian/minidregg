# Linux publication-receipt runtime candidate

This is a source-matched, private Linux build of commit `6776154`'s `native/grain-runtime`, prepared on persvati for a fresh actual Hermes MCP receipt test. It was **not** installed into the active hosted 7801/7803 controllers or their `/agent/grain-runtime` roots.

- Source snapshot: `/tmp/mini-grain-runtime-6776154-src` (only the crate's `Cargo.toml`, `Cargo.lock`, and `src/` copied).
- Isolated target: `/tmp/mini-grain-runtime-6776154-target`.
- Candidate ELF: `/tmp/mini-grain-runtime-6776154-target/release/grain-runtime`, SHA-256 `bde9202275348b6f176c0fe80cafa42e6c60e2cb770341f0e8604fcb2a7bd8c5`.
- Source and output hashes: [source-and-binary-sha256.txt](source-and-binary-sha256.txt). The key changed source is `main.rs` SHA-256 `a8421bf0bdf0c4ba80bcb1adb314c7eaa7213e35a579fe9b5b7a6f3cb11ec2a7`.

The initial `cargo build --release --locked` completed under a transient user service with `CPUQuota=200%`, `MemoryMax=8G`, `CARGO_BUILD_JOBS=2`; its peak was 372.3 MiB with no swap. The initial `cargo nextest run --release --locked -j 2` passed 33/33 tests in the same bounds, peak 268.1 MiB with no swap. The retained [build.log](build.log) and [nextest.log](nextest.log) are immediate **cached verification reruns** under the same bounds, each with systemd success; the test log lists all 33 passing tests. Both commands used `CARGO_TARGET_DIR=/tmp/mini-grain-runtime-6776154-target` and `WorkingDirectory=/tmp/mini-grain-runtime-6776154-src`.

These are component build and test results only. The actual Hermes MCP success criterion is a fresh signed publication whose model-visible `mini_publish` result matches the same runtime journal receipt's `transactionId`, `eventId`, `acceptedCount`, and `imageBoundary`, as well as its prompt/tool operation IDs and publication targets. A separate signed Mini view must establish the task, generation, and content root; those coordinates are not fields in `publicationReceipt`. Field presence alone does not qualify it. The existing hosted workroom continues on its earlier pinned runtime while that separate test is prepared.
