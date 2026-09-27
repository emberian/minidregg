# Exact committed SPK host Linux build

Source was `git archive --format=tar d38c782 native/spk-host native/spk-rpc`, SHA-256
`1ef0c218fd2004c3f6d69c2e3a03cfab61e4f5135cc640fb9e9251539bc8aedf`.
It was extracted independently at `/tank/dregg-build/mini-spk-host-d38c782` on
hbox. `cargo build --locked --release --bin spk-host` finished in 1m51s under a
2-job, 200% CPU, 4 GiB memory scope with an isolated Cargo target.

ELF: `/tank/dregg-build/mini-spk-host-d38c782/bin/spk-host-d38c782`.
SHA-256: `b2826f738323e5e718c191887eb12ae15ae71408df59f5a0ae30d371b5b6c3c5`.
It is an x86-64 Linux PIE, BuildID `7471e866d5b73245a275363e29028951db18beac`.

The committed `main.rs` in d38c782 exposes INSTALL commands but has no
`resident-run` CLI branch, despite the START library code in that commit. This
ELF is suitable for scoped INSTALL acceptance only. A later exact-source build
is required after the CLI registration is committed before START acceptance.
No Store or systemd unit was touched for this build.
