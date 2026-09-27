# Signed observations and physical read guards

Integration finding, September 27, 2026, against the pre-repair source at
`5a76cf9`. The first fresh source-publication fixture refused before source
admission or fn POST. A private source-owned diagnostic found that the packet's
selected content root matched the loaded directory's materialized content root,
while that root differed from the durable physical snapshot root. The public
refusal remains generic; source-side diagnostics must not become an unsigned
participant observation endpoint.

These commitments have different meanings:

- `observed.before.payload.root` identifies the materialized logical resource.
  It belongs in the existing signed observation and selected-content identity.
- `ResourceBirthCodec.physicalRoot (.live observed.before)` identifies the
  physical cell stored at that resource ID. It belongs in the durable intent's
  read guard and must equal `durable.snapshot.model.roots` at that ID.

Do not repair an equality between these two roots by dropping the guard or
changing the signed content identity to the physical root. Derive the physical
root from the exact observed cell, prove its relationship to the loaded bytes
and snapshot coherence, and retain both commitments in their proper roles.
`CanonicalCellRegistry.LoadedPolicySource.readGuard` already documents this
physical-root discipline.

Root's scoped source audit found the same mistaken comparison in the following
pre-repair paths; their owners are repairing them together:

| Path | Incorrect use to replace |
| --- | --- |
| `FnSelectiveReleaseSourceAuthority.prepare` | Inner selected-content root equated with physical snapshot root. |
| `ApplicationShareIssueDelegation.prepare` | Inner application root equated with physical snapshot root. |
| `ApplicationDispatchAdmission.checkRead` and `ApplicationDispatchPending` | Signed observation root used directly as physical guard for four observed cells. |
| `ApplicationLifecycleBeginReceiver` | Signed package root used directly as the physical package guard. |
| `ApplicationLifecycleClaimCurrent` and `ApplicationLifecycleClaimCore` | Signed app/package roots used directly as physical guards. |

This is an implementation defect, not evidence that the signed observation is
invalid. Earlier source compilation and conditional proofs do not demonstrate
that these admission paths can accept a real request. Closure requires the
coherence bridge, updated guard proofs, source-matched native execution on a
case with distinct inner/outer roots, refusal on actual physical drift, and
the original receipt/recovery checks. This note records the finding and repair
contract; it is not completion evidence.
