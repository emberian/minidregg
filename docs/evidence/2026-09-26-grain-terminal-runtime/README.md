# Committed grain runtime image (2026-09-27 UTC)

The Linux runtime was built from an isolated `git archive` of committed
`e213b4f` containing only `native/grain-runtime`, archive SHA-256
`bbb6cd1f6b9d50425c6358b0dffb5c6b779bf9e527c03ae37ef7385045a0b40d`.
The archive excludes shared-tree work in other crates and mutable `target`
artifacts. A bounded user scope used two Cargo jobs, CPU quota 200%, and a
16 GiB memory cap.

Release build passed, `cargo nextest run --release --locked` passed 50/50 tests,
and `cargo clippy --all-targets --locked -- -D warnings` passed. The immutable
executable is `/tmp/minidregg-grain-runtime-e213b4f-evidence/grain-runtime`,
SHA-256 `c95f87a8abad50dc0e4f6c0bb90d62c3b65fc06995df8680ce04d036bfc49b61`.
The [manifest](manifest.txt) and [hash list](sha256.txt) pin the source and
artifact; [build](build.log), [test](nextest.log), and [clippy](clippy.log)
logs retain the verdicts.

The earlier exact `2a42440` archive built and passed 49/49 tests, but strict
clippy flagged two owned-comparison warnings in `legacy_custody_audit.rs`.
Commit `e213b4f` corrected those comparisons and added one focused test.
This record certifies an image for private acceptance; it does not claim a
live runtime swap or a native hosted journey.
