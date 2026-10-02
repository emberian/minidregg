# Coherent current observation batches

This successor addresses an actual joined-world failure: all five shared-name
append planners refused before submission because independent app/task writes
advanced the global world head between room and index reads. Four-to-two scope
reads reduced work but did not solve that dependency consistency problem.

The native batch carries 1 through 16 ordinary observation requests. It creates
all singleton challenges against one Opened image and answers all singleton
signed observations against one Opened image. Every element uses the existing
intent authentication, current exact invoked-grant admission and query projection.
A refused element discards the complete answer; partial results are never returned.
Input and output collections use half the existing host frame bound with a
256-byte reserve, so their canonical hex-JSON presentation fits the host frame. No singleton protocol
bytes or signatures change, and no authority survives beyond the current command.

Shared names bootstrap only an index candidate, then admit the room and candidate
index in one batch and recheck the current pointer. A changed pointer can replan
at most three times; unrelated world writes do not trigger dependency replanning.
Aliases share one coherent chain per room for a listing, with no cross-room head
requirement and no command-persistent memo.

Later reads of an opened name admit the room, index and exact pinned target in
one batch. They compare the current room pointer and the exact name/link/kind/target
or authenticated absence decision. A moved binding refuses, rather than retargeting.
They do not compare the old discovery world's global head to a later target head.
Current invoked scope and salted resource root verification remain mandatory.
Submission and exact recovery remain ordinary retained target-pinned bytes.

The same workspace signed_views helper returns existing singleton signed-envelope
paths for app readiness's five current resource reads, preserving source194's
ordinary singleton observation predicates. Shared references expand into admitted
room/index guards deduplicated only by exact kind, target and invoked capability
inside this batch; each original binding is checked before returning its tuple. That consumer is owned by the experience
lane and is a separate integration checkpoint.

Ephemeral shared reads track the real batch attempt and every created query source,
then clean their owned custody after recording the read journal. They create no
unused outer attempt and perform no redundant outer receipt-floor load.

Verification at this checkpoint: 17 focused shared-name Rust tests pass
(log /home/ember/build/codex-bigstep-latency/rust-batch5.log). They
cover old exact-recovery cases plus current unchanged projections under unrelated
head advancement, retarget/removal/changed link/pointer/narrowing/wrong grant,
new binding after prior absence, and missing guards. Source review is clear for batch admission and name projections; the latest guarded
multi-view expansion is being reviewed. Integrator requested this checkpoint release
without a duplicate Host.Json build. Native source compilation,
actual joined dynamic-name receiving under writers and timing qualification are
separate pending checks; this note makes no measured batch speedup claim.
