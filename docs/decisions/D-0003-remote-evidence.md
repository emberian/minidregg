# D-0003 — Isolated remote checks and evidence

- Status: accepted
- Date: 2026-08-09

## Decision

Use `hbox` and `persvati` as isolated CPU proof/build workers. Every run names an explicit commit,
transfers its hashed `git archive` into a unique writable run tree, verifies an independent SHA-256 source-file
manifest and the Lean/Lake/Rust pins, applies CPU/memory/time limits, and records exact source,
dependency-revision, raw-log, source-integrity, and project-olean manifest hashes.

The dependency seed is keyed by the full Lean-toolchain and Lake-manifest hashes, constructed under a
host-local lock, checked against every pinned package revision, and made non-writable. A run gets a
run-local directory tree with read-only hard links to seed files and private copies of Lake's small mutable
hash/trace metadata. There is no `.lake/packages` symlink, writable shared package worktree, shared project
build output, or dependency on a pre-existing repository checkout. Seed construction is serialized; builds
against a completed immutable seed are concurrent.

`scripts/remote-check.sh` is the canonical entry point, with the required form
`scripts/remote-check.sh HOST COMMIT -- COMMAND [ARG ...]`. The command is transferred as an exact
argument vector and `elan`, `lake`, `cargo`, and `rustc` paths/versions are recorded absolutely. Evidence
defaults outside the worktree and the script rejects an in-repository evidence directory. The stale
checkouts already present on both machines are never used as source or dependency candidates. Neither
current GPU has a usable compute stack, so GPU claims require a separate environment decision and evidence
record.

The source copy is writable because checked Lean generators intentionally rewrite committed artifacts while
compiling. After the command, the runner hashes every source file again and compares the complete sorted
manifest, so changed, deleted, and newly created files all fail by default. Root `.lake` and the separately
located Cargo target are build state and are outside that comparison. A caller may repeat
`--allow-generated PATH=SHA256` to admit an exact normalized path at an exact expected content hash; every
such path must exist after the command and match its declared hash. Both manifests and the allowlist are
evidence artifacts. The runner never copies generated output back into a worktree or derives an expected
hash from the generated result.

## Claim ceiling

A successful record proves only that its exact explicit-commit snapshot, exact dependency revisions, and
post-run source-integrity policy completed its exact command on the recorded environment. With the default
empty allowlist, pre- and post-source manifests are byte-identical. An opt-in generated output is claimed
only at its caller-declared path and SHA-256. This is not a benchmark, Rust semantic/refinement claim, or
cryptographic security claim.

## Revisit trigger

Revisit when a hermetic build system replaces Lake's package tree, when usable GPU compute is
installed, or when remote patch-mode experiments are required. Patch mode must record base commit
and patch SHA-256 and may never silently promote its result to committed-source evidence.
