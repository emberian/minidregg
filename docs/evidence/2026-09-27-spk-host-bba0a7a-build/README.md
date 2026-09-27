# Exact committed callable START CLI build

Source: `git archive --format=tar bba0a7a native/spk-host native/spk-rpc`, SHA-256
`f998099b680ef0e34e9c6ec065dd130c4d69f5bf11b12f1fff712d65a9a040dc`.
The independent hbox source and isolated Cargo target are under
`/tank/dregg-build/mini-spk-host-bba0a7a`. A 2-job, 200% CPU, 4 GiB memory
scoped `cargo build --locked --release --bin spk-host` passed in 40.74s.

ELF: `/tank/dregg-build/mini-spk-host-bba0a7a/bin/spk-host-bba0a7a`.
SHA-256: `1d85b2f21039bc228262ca6a1b0bf52a0c26688f9a7324588d3fbde3679dd2e4`.
It is an x86-64 Linux PIE, BuildID `c241746758f8156c1cec06a68e8232d03d8d98f9`.

The read-only CLI dispatch probe `resident-run` with a deliberately absent
config exited 1 and printed `spk-host: resident refused: native attempt
directory is not owner-private`; it reached the resident handler rather than
the usage branch (exit 2). No Store, volume, or systemd unit was touched.

This proves source, build, and CLI reachability only. Fresh v3 lifecycle
INSTALL/START acceptance against a source-qualified Host remains separate.
