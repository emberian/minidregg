# Committed Linux Rust artifacts (2026-09-27)

These are separate, source-qualified release builds on Persvati. The qualified executables were copied to hbox under `/tank/dregg-build/`, set to mode 500, and SHA-256 checked after transfer. No service was installed or started in this build lane. These are build qualifications, not a native journey or deployment verdict.

| Executable on hbox | Source commit | SHA-256 |
| --- | --- | --- |
| `/tank/dregg-build/minidregg-grain-runtime-18166e5/bin/grain-runtime` | `18166e5` | `7295fa222c288ad39aa5c6d97ef4f72ce5792e0f41413fb5d4e254eeba219187` |
| `/tank/dregg-build/minidregg-grain-runtime-18166e5/bin/grain-provider-bridge` | `18166e5` | `2877ef2a5293ee0b2a7c22d0c0216dab865d3174dd68b312889661cb4f90cfcb` |
| `/tank/dregg-build/minidregg-resource-client-18166e5/bin/mini` | `18166e5` | `4a9625cfad8f564fd69b1468bdf1114b05f441abc26ec259dff67b68c5d58cec` |
| `/tank/dregg-build/minidregg-spk-host-9f1fded/bin/spk-host` | `9f1fded` | `a03253d6267d248cb7c0dce0b8104c551750a903abd32e3650e9297fde2a9d62` |

The read-only source archives were limited to the relevant committed crates and their path dependencies. Their archive SHA-256 values are `48e2fbff7d8cbcfc7580462af000e27c01339f77ad11b7e753c1aad247c33d8d` for grain-runtime, `dcda60f923df816bd78fa039cb21c1ad3562ce85baca24613abd48d6a95eff40` for resource-client, and `5cdad4408fa4e89839abb1540b6afc5ca60fb06f5a3eadaeb8741fcf5767af23` for spk-host. Extraction and source readback covered 37/37, 33/33, and 95/95 files respectively; the per-file manifests and verification output are retained here. The archive source identity, not copied `.git` metadata or the shared working tree, qualifies each build. The spk-host lock selected the `sandstorm-package` Git dependency at revision `5819115352bdfa43c5cbd329727d4f8d8a1b5be9` (visible in its build log).

Each build ran `cargo build --release --locked --offline` with `CARGO_BUILD_JOBS=2`, a private target directory, and a bounded systemd user unit (CPU 200%, memory 4 GiB). The selected binaries were `--bins` for grain-runtime (runtime plus provider bridge), `--bin mini` for resource-client, and `--bin spk-host` for spk-host. All three units finished successfully; see the retained build logs. The earlier source-exact Rust tests and Clippy checks belong to their source-owner evidence; no tests were rerun solely for these artifact copies.

The `*-binary-sha256.txt` files record Persvati link outputs. The hbox hashes above were independently read back after transfer. `SHA256SUMS` covers the portable evidence files in this directory, not the executables.
