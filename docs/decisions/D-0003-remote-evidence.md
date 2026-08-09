# D-0003 — Isolated remote checks and evidence

- Status: accepted
- Date: 2026-08-09

## Decision

Use `hbox` and `persvati` as isolated CPU proof/build workers. Every run transfers a hashed
`git archive` of one clean commit into a unique run tree, verifies Lean/Lake pins, uses a locked
dependency cache keyed by those pins but no shared project build output, applies resource limits, and records
raw output plus environment and project-olean hashes.

`scripts/remote-check.sh` is the canonical entry point. The stale checkouts already present on both
machines are quarantined and never used as source. Neither current GPU has a usable compute stack,
so GPU claims require a separate environment decision and evidence record.

## Claim ceiling

A successful record proves only that its exact committed snapshot completed its exact command on
the recorded environment. It is not a benchmark, Rust semantic/refinement claim, or cryptographic
security claim. Generated-file checks additionally require byte equality with committed outputs.

## Revisit trigger

Revisit when a hermetic build system replaces Lake's package tree, when usable GPU compute is
installed, or when remote patch-mode experiments are required. Patch mode must record base commit
and patch SHA-256 and may never silently promote its result to committed-source evidence.
