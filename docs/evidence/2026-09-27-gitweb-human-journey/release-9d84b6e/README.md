# Exact committed GitWeb human-journey release bin

The new `gitweb-human-journey` executable was built from the exact committed `9d84b6e` SPK subtree, limited to `native/spk-host` and its `native/spk-rpc` path dependency. The read-only Git archive SHA-256 was `6818e16f1ef58e7499c0390c33ac714b5ca39808a45b92f52c26f655587fe687`. Relative to committed `8d7a3f8`, the sole crate source addition is `native/spk-host/src/bin/gitweb-human-journey.rs`, SHA-256 `71170393aed441bb86a411765785dc976aeed74b66328f45064b3a0861112991`. The [source manifest](source-sha256.txt) SHA-256 is `6e4104985df79f13dcc78c3a8a6bd5cff347769db86f16e3974a6e51bb2a3b9e`; all 96/96 extracted source files passed readback. No shared-tree sandbox or spawn-gate WIP entered the archive.

The independent Persvati build ran in user unit `minidregg-spk-gitweb-9d84b6e-r1.service`, invocation `9999686f80cf404bb720ddc233d0de0e`, with `CARGO_BUILD_JOBS=2`, CPU quota 200%, memory cap 4 GiB, and a separate target directory. Exact command from `/home/ember/build/minidregg-spk-gitweb-9d84b6e-src/native/spk-host`:

```sh
cargo build --release --locked --offline --bin gitweb-human-journey \
  --target-dir /home/ember/build/minidregg-spk-gitweb-9d84b6e-target
```

The unit terminated successfully; [build.log](build.log) records the release-link verdict after 18.99 seconds. Rust toolchain: `rustc 1.98.0-nightly (13f1859f2 2026-06-27)`. The linked Persvati executable is `/home/ember/build/minidregg-spk-gitweb-9d84b6e-target/release/gitweb-human-journey`, SHA-256 `bc0e40e87101ab8413eea5e8b0604e4e34acac48d90bfa89b53c919e24f7af18`.

A readback-identical, owner-readable/executable mode-0500 copy is staged at `/tank/dregg-build/minidregg-spk-gitweb-9d84b6e/bin/gitweb-human-journey` on hbox. The adjacent protected [hbox manifest](MANIFEST.txt), SHA-256 `b7520b71c0cfe35c79b47b7afe407dc5d8c7577fc66c50fadd26186a5e60823b`, pins the source archive, complete source list, build unit, and ELF. This release artifact is ready for an isolated component probe; no service was installed, Git request made, resident START attempted, or live Store changed by the build lane. The parent directory's focused source-check logs remain the earlier source verdict and were not rewritten.
