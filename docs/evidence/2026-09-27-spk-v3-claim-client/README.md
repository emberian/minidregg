# Staged v3 launch claim consumer

`lifecycle_v3_claim_native.rs` stages the source-owned op68 plan and detached
op69 assembly for an exact accepted v3 BEGIN. It compares the inspected plan
against the retained original BEGIN ingress and receipt coordinates, the
qualified v2 launch descriptor/root, source volume ID, selected first-create
command, and protected management signer pins. A parent active marker is
written before the first current-image invocation. An uncertain response must
be recovered from that original attempt; no second claim attempt is permitted.

This consumer does **not** submit op26 or authorize physical INSTALL/START.
The op68/69 Host routes and fresh event24 committed-v3 inspection are still
under source qualification. Event25 completion authoring is not yet available.
The existing INSTALL/START guards remain closed. The retained receipt fields
are a comparison to the source plan, not a physical volume-root witness or
a claim that the v3 event was accepted.

Hbox isolated Rust snapshot used `CARGO_BUILD_JOBS=2`, `MemoryMax=4G`, and a
private target. `claim-focused-r2.log` records 13/13 scoped nextest passes,
including rejection of altered original receipt, volume ID, launch root and
selected command. `claim-clippy-r4.log` records strict all-targets Clippy pass.
These are component checks against the draft wire, not an end-to-end Mini
native or Store execution.
