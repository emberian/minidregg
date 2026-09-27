# Checked lifecycle completion: report-source checkpoint

`Kernel/ApplicationLifecycleCompletionReport.lean` defines a strict framed
physical-custodian report and a separate strict stop audit. The report repeats
the full committed v2 claim projection; its source check binds the original
BEGIN, signed SPK descriptor, intended unit and image, outcome-specific host
facts, and exact prospective Mini Manifest bytes. The detached Ed25519 signing
frame binds deployment domain and installed semantics. A private `Checked`
constructor is issued only after the configured native signature verifier
accepts the pinned public key and exact report preimage.

`Kernel/NativeHostContext.lean` adds an optional 32-byte completion-custodian
public key. Absence preserves the prior runtime-parameter preimage. Enabling it
changes semantics and therefore requires a separately qualified genesis/profile.
Deployment must assign the custodian a key distinct from resource-owner and
controller keys; the present source pins a separate configured key slot but
does not prove that byte-level inequality against the authority catalogue.
Mini can verify its signature
and source/state binding, but the truth of systemd, cgroup and immutable package
observations remains an explicit physical host trust boundary.

Both source files passed a bounded direct Lean check with `LEAN_NUM_THREADS=2`
against the committed lifecycle-v2 coherent OLean snapshot at
`persvati:/home/ember/build/minidregg-overnight-20260927-selected-prefix-codec`.
The local source was copied to independent `/tmp` files; no OLean or source in
the shared warm snapshot was edited. Source SHA-256:

- `ApplicationLifecycleCompletionReport.lean`: `0349ba18eb51fc72de34719540f8191f5f8795c8da80863890e9bf6d92fce661`
- `NativeHostContext.lean`: `e88927f66ab0b1e806e9842e6d67c0f74b551a433acd83318eeeb0bd81c036d4`

This is a source checkpoint only. It does not expose the reserved completion
policy slot, authorize a fresh completion command, write the installed Manifest,
or deliver a host launch. Those require a special joint DRC admission and one
exact CAS/readback with authenticated historical BEGIN and claim provenance.

### Current source-only completion admission checkpoint

The following uncommitted lower modules were checked in dependency order in
the independent Persvati overlay `/tmp/minidregg-completion-src` against the
committed lifecycle-v2 Replay and NativeHost context. These checks establish
type-correct source admission and intent construction only; no event-18 native
route, CAS receiver, operator report signer, or physical completion has run.

| Module | Source SHA-256 | OLean SHA-256 |
| --- | --- | --- |
| `ApplicationLifecycleCompletionPolicy` | `0930f54ccf1f7c754975df4dd54cbd00c41111afbf1237182fadc76acd8567ce` | `035fc4734bee1876938e1c5317c6a2971a7678259366f37260a8bf195c354bb1` |
| `ApplicationLifecycleCompletionSource` | `5cd6cbd960c4dfdfdbc477320bde14d4034e0a7b79f477aaef0b4f122b6be3c6` | `a283c31abde34291285476fb16d7aad21dda1c7a1eb8066efde35d54daea520a` |
| `ApplicationLifecycleCompletionIngress` | `fb089fc56f4d19f98bf7c471abc39cdbd13e00e21a88551bba587185e2364375` | `66d4f3b76ac14b4e447ae41742736bfdd3266b0aeafb0dcb8839711e05af3b4d` |
| `ApplicationLifecycleCompletionHistory` | `da15f060ca7f71b9943f11863bf95c08d588fb4f155399316d11adffc3d1eef4` | `f06de4112cac6af45d06c4de4fda22569d3829d1e0044a7592051cfcef98ad24` |
| `ApplicationLifecycleCompletionAdmission` | `cd264b7b2915fec9e896fbf24af585c107c329644bb13e9ebbe05db12b56967e` | `97898f18e3f9f12f5670761f0e0ebe2fb0b49130a3cb75e1db5b0552b2198e11` |
| `ApplicationLifecycleCompletionCore` | `49c8059de00466d3d8318034a281ef9159ab39b6e0a31a2b9449e1d4d320aae1` | `79ad51f7a58f233cfdbc62c40127f96492b3f881f097db583ef132eeeeb0ed23` |

`Admission.prepareConditional` requires a conditional exact-prefix v2 claim re-admission and
full record match, current app and
package cells, separately signed package observation, current management
law, DRC target signatures, and the configured physical custodian key. `Core`
preserves DRC writes/authority guards, emits event family 18 and a second
one-use report nullifier, and pins the read-only package cell to its physical
CAS root for start/stop. The new storage charge counts actual DRC post-write
bytes and the replacement event/nullifier, rather than a second ordinary
event. The lower historical candidate does **not** prove that the surrounding
history was admitted; Replay must match it to a claim retained by its same
chronological admitted walk, and the live receiver must use a `Verified` tip.
Only that future verified receiver may submit this intent.
