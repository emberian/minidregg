# Dedicated dispatch purse: source contract and bounded stage

The agent parent is an exact no-op witness. Its reserved prompt allowance is not
an HTTP request budget. `Kernel/AgentGrain.lean` gives an independently attached
task the same reserve and settle transitions used for MCP work; its units are
permission micro-units, not HTTP bytes or measured CPU. A configured fixed
reserve and fixed charge may pay for one dispatched request. Physical CPU and
memory remain governed by the systemd units and are not attested by that
charge. `docs/HOSTED-PROVIDER-CUSTODY.md:84-91` states the analogous independent
provider-purse rule.

The current hosted controller has one parent, one MCP `toolTask`, and one
provider task. The MCP tool task cannot be reused as a per-agent HTTP purse:
its hold and pending attempt cover separate tool operations. A fourth
`dispatchTask` custody slot must be configured for each fixed agent caller
(or a deliberately serialized one-caller controller). It owns a distinct
AgentGrain task, subject, signing key, current capability, observe capability,
reserve and charge. A browser/API token only selects its fixed custodian; it
never chooses the purse, ticket, parent or signer.

For each agent request, the runtime must retain the exact canonical request
bytes/digest and a unique operation ID before any external send. It must
write a durable hold marker, submit the ordinary signed AgentGrain reserve,
and require its exact confirmed native transaction/event/image receipt.
The reservation must be tied to the request/operation in its signed context;
a current page with `status=3/4` and matching amount alone could describe a
different outstanding operation. The v2 special dispatch admission must join
that verified reserve, its live task/generation/root and signed no-op witness,
the current prompt parent task/generation/root and no-op witness, and the
historically issued app ticket/current app/session/permission law in one
verifier-opened image. The app ticket grants interface rights; the separate
dispatch purse pays for the attempt. Neither substitutes for the other.

The physical host must compare the checked v2 projection against the fixed
custodian and current app/parent/dispatch task generations and roots under
its app lock immediately before fd3. It records a one-shot send marker
before writing to fd3. A definite app reply can be settled with the fixed
charge through the ordinary AgentGrain transition; a definitive refusal
before send can be settled at zero. An uncertain write, reply, native CAS or
settlement retains the exact attempt and reservation, blocks another send,
and requires lookup/reconciliation. It cannot be retried from an old permit.
Hard EOF must stop/fence the caller unit, trip the parent generation, fence
the dedicated dispatch task, and retain unresolved holds. The physical host
must also reject any stale process-generation/InvocationID or changed task
root. A Mini point-in-time permit is not a lease that cancels a later fd3 call.

`Kernel/ApplicationDispatchAgentPurse.lean` reads the *separate* current
reserved AgentGrain page from the same opened image, checks configured
generation/amount/charge, and retains the full state plus signed inner and
physical roots. Source SHA-256 `ef4b823b0ec96a96bab5c2ecfdb3a5391b8191b435642e130ae45d6560fcd2db`;
source-matched OLean SHA-256 `8c918b8d02e0ce7fa030d71e68c44f6d32aa5b0d8d6ef62c2a63e60e7845210f`.
`Kernel/ApplicationDispatchAgentReserve.lean` selects one actual
verifier-retained original prefix, decodes and natively re-admits its ordinary
signed AgentGrain reserve, requires one exact purse target and a nonce bound
to the complete HTTP request digest and a distinct reserve operation ID, compares the *full*
durable intent and receipt IDs, and proves membership in the verified current
history. Its `current` check requires no later admitted write of the purse
cell, plus the same reserve post-state and cell roots at the current tip;
this excludes a write-and-restore suffix. Source SHA-256
`9bd1c96a01f072570932c7a01b3b7c097afa8342e51a06581921421d9a052c03`;
OLean SHA-256 `90c9e24921183041766b0e75729bb61002690f83c08b7c50f731f31784e1bcfb`.
Both remain source selections, not delivery permits. Serial direct Lean exit 0 in private plain-copy
`/home/ember/build/minidregg-dispatch-final-20260927-spkcompat` with
`LEAN_NUM_THREADS=2`, `MemoryMax=64G`, `CPUQuota=200%` and command
`lake env lean Kernel/ApplicationDispatchAgentPurse.lean -o .lake/build/lib/lean/Kernel/ApplicationDispatchAgentPurse.olean -i .lake/build/lib/lean/Kernel/ApplicationDispatchAgentPurse.ilean -c .lake/build/ir/Kernel/ApplicationDispatchAgentPurse.c` then the same command for `Kernel/ApplicationDispatchAgentReserve.lean`.
The final Reserve direct Lean command exited 0 with an empty log
`/tmp/dispatch-agent-reserve-final.log` (SHA-256
`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`).
Its imported `NativeReserveContinuity` source SHA-256 was
`3a0c8923693d275f140ae74d69632c9b7f3b56877564a48f74f9d6dfe7f6cfc1`,
OLean SHA-256 `40d951a03aa0e42f363104544184c18a1f9a281d741bb79f46de455a75d7acfc`.
Earlier logs `/tmp/dispatch-agent-purse-narrow.log` SHA-256
`5d01eace000c253763fefae7a12909c05ee10a36006cac20dc444bae5761418d`
and `/tmp/dispatch-agent-reserve-narrow.log` are superseded by the final selector check.

The separate grain-runtime implementation has four changed source files:
`main.rs` SHA-256 `7746277844e0cfb419d9cba2cf670a9d5e28b483c3f8b7a489c0eac21ff2f4de`,
`dispatch_custody.rs` `0f648751a1ea72d2789e0e9de1c1dbd9c6a05c9eb8167d7bab3d4a5ed4a4e7a1`,
`dispatch_runtime_tests.rs` `fc7377d07a2d9b8f723967c2f0235b6752a16654d85d58403b8af850f7d50db8`,
and `publication_refusal_tests.rs` `0d13096308d1509c3168fb07630cd11a8b79b3b131afe80b153eb11f58c939cf`.
The task owns its own signer, native hold and Unix socket initialized at
0600, then granted only one fixed SPK-host UID by a checked named-user ACL;
the final effective mode reflects the ACL mask. The socket ancestry resists
attacker rename, and both sides check peer identity and inode. `reserve` returns an exact
confirmed receipt, selected history index and retained request hash. `mark-send`
durably closes the no-send abort path before fd3; definite response may settle
the fixed charge, while uncertainty and hard EOF retain the hold. Parent hard
EOF fences only this caller and dispatch task, never the shared app unit.
Fenced restart recovery also fences this task. A late EOF during native
pre-send queries refuses mark-send; once the durable send marker exists the
attempt stays uncertain. The zero-charge no-send release saves its phase
before settlement, so a crash after confirmed settlement clears the hold can
recover that exact attempt. A settlement receipt pins the signed source,
call and outcome bytes and must be confirmed by a fresh native lookup after
restart. A missing or tampered receipt keeps the attempt unresolved. If a
confirmed dispatch hold survives hard EOF, recovery retains Fenced mode for
the private operator action `reconcile dispatch audited fixed` or `zero`;
that decision is durable before an ordinary signed settlement. It never
resends to the app or infers zero charge from timeout. A pre-reserve attempt
with no hold/pending can clear only after signed idle state; a confirmed
settlement can clear only after exact receipt lookup. Failed socket setup
removes only the socket inode bound by this process.
The intermediate hold marker with no submitted reserve, or a definitive
native reserve refusal, also clears only against signed idle state. If a
reserve confirmed before the wrapper saved its operation/generation/postroot,
audited recovery pins the source JSON hash saved with the confirmation,
checks its exact task/subject/context/amount/before root, retained native
call/outcome hashes and receipt, then runs a current native receipt lookup.
This reconstruction is audit-only; it never enables mark-send. A saved
no-send-release phase with a still-held reserve can enter only zero-charge
audited settlement. The returned reserve operation ID is derived from the
confirmed signed attempt path, not guessed from the next local counter.
The Linux source snapshot `/tmp/dispatch-grain-runtime-20260927` used isolated
target `/tmp/dispatch-grain-runtime-target`; `cargo fmt --check` passed and
`cargo nextest run -E 'test(/dispatch_runtime_tests|dispatch_custody/)'`
passed 3/3, including simulated pre-submit, post-reserve/pre-metadata,
no-send release, settlement crash, tampered receipt refusal, EOF-during-query,
fenced restart and audited settlement windows. Captured log
`/tmp/dispatch-runtime-final-crash-nextest.log` SHA-256
`77b527a3369af7779b7eca891e7eef2b0058f49d226a6a6f92cdd432f2173b83`.
`cargo check --bin grain-runtime` passed in the same isolated target; log
`/tmp/dispatch-runtime-final-crash-check.log` SHA-256
`d8c723b7b05d8c668c0fb6c63066389f939e587236667127643ff4ff06b8f39a`.

The source `requestSafe` bound is 8 MiB body, at most 128 headers each with
128-byte name and 8192-byte value, and 8192 combined path/query bytes.
Together these payloads are under 9.5 MiB before small canonical length/tag
overhead; the runtime retains at most 10 MiB canonical request and the JSON
RPC admits 22 MiB for its lowercase hex representation. The runtime further
limits operation IDs to `u64`. The source-owned v2 admission must compare
the exact retained bytes and digest and join the original reserve, parent
generation, app ticket and current grants. A draft v2 receiver was removed
after review found event11 had no reserve claim/nullifier or purse physical
guard; event family 21 is reserved for a new replayable, one-use paid agent
dispatch. There is no v2 delivery permit,
host agent route, or actual SPK app delivery in this cut.
