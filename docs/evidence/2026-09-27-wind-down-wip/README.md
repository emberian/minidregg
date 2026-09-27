# Frozen source at the user-requested wind-down

Ember requested winding down at 10% remaining usage on September 27. No new
native runs or implementation tasks should start until resumed. The approved
long direct birth retry was **not launched**. Its exact original attempt and
genesis Store remain preserved; the latest exact lookup returned `absent`.

These patches preserve unfinished controller/resident source without treating
it as root-reviewed integrated functionality. They apply to `base-commit.txt`;
`source-sha256.txt` identifies the resulting 13 source files. Existing shared
working-tree edits remain in place. **Do not apply these patches over that WIP.**
Use a separate plain scratch copy of the named base to inspect/reconstruct them.
No branch, reset, stash or worktree operation is needed.

- `controller.patch`: lifetime reserve/payer custody, exact paid-plan/ingress
  and committed-receipt joins, durable mark-send, settlement and definite-reply
  gating. The lane reports 125/125 component tests and strict Clippy passing.
  Independent review and native integration remain separate obligations.
- `resident.patch`: reverse reserve/payer transport, separate app/grant signer
  custody and source op78/79 assembly. Eight focused component tests and strict
  Linux Clippy passed. **Fresh op76, durable mark-send integration, fd3 delivery,
  settlement and a callable v3 listener are still missing.**

The committed detached payer helper (`fa581ae`) and Fenced-only STOP recovery
(`1ec2fc0`) are already in the base. The callable complete STOP supervisor has
not been implemented. Foreign sandbox/spawn-gate, compiler/prover, licensing,
old Python and other unrelated WIP are deliberately outside these patches.

Resume through dregg-assortia's HANDOFF.md and the next wind-down checkpoint.
Complete integration and inspect actual native outcomes before claiming a
hosted agent or two-participant application service.
