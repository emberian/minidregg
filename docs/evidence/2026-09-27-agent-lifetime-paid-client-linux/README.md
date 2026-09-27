# Exact d752df7 Linux resource client build

An isolated archive of commit `d752df7` was built on Persvati with `CARGO_BUILD_JOBS=2 cargo build --release --locked --manifest-path native/resource-client/Cargo.toml`. The release build passed and the resulting `mini --help` command exited 0. The archive is separate from the shared working tree.

Private build root: `/tmp/minidregg-d752df7-resource-client-build` on Persvati. The source archive SHA-256 is `56dae26ea411c6fbda82e399d87f1716edfb2b18336d4bbfc6853586d0c1543f`. The Linux ELF is `target/release/mini`, SHA-256 `08a1605a804cab92fd262bf82e951e9c2b3c1573d2ba8a593ff97888962d7acf`. The archive's `main.rs` and paid custody source hashes match the committed client cut. `build-manifest.sha256` pins those inputs, the ELF, and the retained build log.

This is client image/source qualification only. No Host or Mini Store was changed, and no event 27 or event 26 native acceptance follows from the build.
