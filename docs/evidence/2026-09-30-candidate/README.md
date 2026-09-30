# Reproducible candidate from a git archive, 2026-09-30

`deploy/candidate/build.sh` was run on a clean directory holding only a
`git archive` of commit `45a9974` (branch `m7-candidate`), on a development
Linux x86-64 machine (24 CPUs; load 5–7 during this run). The exact driver is
[`fresh-procedure.sh`](fresh-procedure.sh), run as

    M7_REFERENCE=$REFERENCE/manifest.json JOURNEY_GROWTH_LEVELS=10 \
      fresh-procedure.sh source-45a9974.tar $FRESH

`$FRESH` and `$REFERENCE` stand for the machine's directories; `$ELAN_HOME` and
`$CARGO_HOME` for the toolchain managers' homes. Paths in the copied files
below were rewritten to those names; nothing else was edited.

## Result

| binary | SHA-256 | independent reference build | recorded pin |
| --- | --- | --- | --- |
| `minidregg-host` | `723940446d3e0256bd446b07ca8d67ea9d67295d8c7cc78e08bb2487ffbe3db2` | same | **same** as the qualified `e22d16b` Host (Host sources are identical) |
| `mini` | `6e74ad4339fea4c36cd03e2787657dcfda43aa46c57d54c2944d4d5dbb5d03b5` | same | differs from `0007925` (`3e9cb1ca…`): client source changed since, and see below |
| `minidregg-link-sqlite-store` | `599bc4e6c1a04ab42e4ec4c18f4d47423e9df903006bba1ac2c2b880ff29fbfd` | same | differs from `776ba59` (`ad03aede…`): compiler, see below |
| `minidregg-credential-signature-verifier` | `f95f119664a028c15de26687b7853a5ae1e4982a83c14165afbd59ad9ec67336` | same | differs from `776ba59` (`c8400412…`): compiler and path remapping |

The reference is an earlier full build (`git archive` of `8e57b9d`, whose
compiled inputs are byte-identical to `45a9974`'s: the M7 step compares the
file lists) in a different directory. A third build of only the Rust binaries,
from a third directory, gave the same three Rust hashes.

**Why the recorded Rust hashes differ.** The recorded `776ba59` helpers and the
`0007925` client carry `rustc 1.98.0-nightly (13f1859f2 2026-06-27)`, the
machine's floating `nightly` channel; the source pins `nightly-2026-06-21`
(`8b6558a02`). rustup picks a toolchain from the working directory, and those
builds ran where no `rust-toolchain.toml` was visible. Rebuilding the two
helpers from `git archive 776ba59` with `cargo +nightly` reproduces
`ad03aede…` and `c8400412…` exactly; with the pin they are `599bc4e6…` (Store,
also the candidate's) and `71b8d734…` (verifier without path remapping). The
candidate names the pin on every rustc/cargo call and refuses a binary that
does not carry the pinned compiler string.

## Timings (`timings.tsv`, seconds)

| phase | s |
| --- | --- |
| build (total) | 1797 — Lean packages + mathlib cache 117, native Host 1629 (363 modules, 3296 link objects), Rust 46 |
| verify `SHA256SUMS` | 0.5 |
| `run.sh init` (key, genesis, bootstrap) | 9.5 |
| `run.sh start` | 0.9 |
| `run.sh sponsor` | 1.9 |
| `run.sh stop` | 0.9 |
| journey (`native/resource-client/journey.sh`) | 162.3 |
| acceptance fixture via `newparticipant-from-manifest.sh` | 14.5 |

Earlier full builds of the same inputs under heavier load (18–35) took 4306 s
twice and 1996 s once.

## Journey (`journey.out`, `journey/journey-result.json`)

The single journey from `mj-journey` `521c0e3`, unmodified, with this lane's
`journey.d/m7.sh`: J0–J8 PASS; G FAIL only because `JOURNEY_GROWTH_LEVELS=10`
leaves level 1000 unmeasured (at 10: write 4.0 s, reopen 8.3 s); K4 FAIL (a
declared page holds 4 entries); M3–M6 UNBUILT (other lanes); **M7 PASS**
(`journey/steps/M7/m7-result.json`): candidate files match `SHA256SUMS`, the
journey ran exactly the candidate's binaries, no input under `/tmp`, all four
hashes reproduce the reference from identical compiled inputs, and the
candidate's `run.sh` initialized, served, answered the sponsor's signed read
on, and stopped a second Store. FRONTIER: G.

## What was not exercised

The printed systemd unit (`example.service`) was generated, not installed.
Only Linux x86-64 was built. The run used the network for the Lean
toolchain, the pinned Lean packages, the mathlib cache and crates; an offline
build needs those mirrored.

Every service started here was stopped (`stop.out`, `acceptance-stop.out`,
the M7 step's `run.sh stop`).
