Mini 6d34efd120c4a7365614531beca63cf69390ca90 Linux Rust artifact closeout

Source: read-only git archive of exact commit, scoped to native/spk-host,
native/spk-rpc, native/grain-runtime, and native/resource-client.
Archive SHA-256: 4ca5219bd6645e076b6f0db2b6ad1cdc00529152533382b78f2cc42413a37a52
Source-file SHA manifest: evidence/source-files.sha256
Build host: hbox, x86-64 Linux; isolated source and target under this directory.

Exact build commands (sequential, from this directory):
export CARGO_BUILD_JOBS=2
export CARGO_TARGET_DIR=/tank/dregg-build/minidregg-6d34efd-rust-closeout/target
cargo build --release --locked --manifest-path source/native/spk-host/Cargo.toml --bin spk-host
cargo build --release --locked --manifest-path source/native/grain-runtime/Cargo.toml --bins
cargo build --release --locked --manifest-path source/native/resource-client/Cargo.toml --bin mini

All three release build logs end with Finished. Four ELF binaries were copied to
bin/ and read back byte-identical to their target/release inputs. Exact binary
hashes are in evidence/immutable-binaries.sha256; build and manifest hashes are
in evidence/evidence-files.sha256. Existing Rust tests were reported green by
source owners and were not repeated for this artifact closeout. No service was
installed or launched. No Lean build or shared source edit was performed.
