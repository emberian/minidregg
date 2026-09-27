# Linux Rust artifact closeout — Mini `6d34efd`

Exact source commit: `6d34efd120c4a7365614531beca63cf69390ca90`. A read-only Git archive containing `native/spk-host`, `native/spk-rpc`, `native/grain-runtime`, and `native/resource-client` was extracted into an isolated hbox tree. The archive SHA-256 is `4ca5219bd6645e076b6f0db2b6ad1cdc00529152533382b78f2cc42413a37a52`. The complete source hashes are in `source-files.sha256`, with paths relative to the Mini repository root. `source-files.remote.sha256` preserves the original build-tree paths.

The three sequential `--release --locked` builds in [commands.txt](commands.txt) finished successfully with `CARGO_BUILD_JOBS=2`. Four Linux x86-64 ELF binaries were copied byte-for-byte into the isolated `bin/` directory and checked against [immutable-binaries.sha256](immutable-binaries.sha256):

| Binary | SHA-256 |
| --- | --- |
| `spk-host` | `c937648b5ce4d60c0df4f04176865933ea83bbf4f91026b9fa8b529124ddacf9` |
| `grain-runtime` | `1eede957878146d6ad50f0d5394e4d29d9234773c2f983d439b91792c4641dc9` |
| `grain-provider-bridge` | `86fe0e5a28b05cf3d64952c158757d5a896a022c2d030b322110e167dab8cd52` |
| `mini` | `c157ed5d696318d92d0ddd0ff469838f8e41089a80afe8a418fa53f0851d3db6` |

The binaries and source archive remain outside this repository at `/tank/dregg-build/minidregg-6d34efd-rust-closeout/` on hbox. This evidence directory contains no executable or archive. To verify source hashes, extract the exact commit into a scratch directory and run `sha256sum -c /absolute/path/to/source-files.sha256` there; the shared worktree may contain later WIP. Run `sha256sum -c SHA256SUMS` inside this evidence directory to check the portable logs and manifests. `evidence-files.remote.sha256` preserves the build-host checksum record, whose paths and source-manifest hash differ from the portable copy.

No tests were rerun for this artifact closeout; source owners reported the relevant earlier tests green. No service was installed or launched, and no Lean build was run.
