# Resident START completion preparation (source component)

The resident supervisor now checks its exact systemd MainPID, InvocationID,
ControlGroup and child cgroup before consuming the one-shot lifecycle claim.
It compares the retained signed SPK to the Mini committed-v2 claim, starts one
bounded app child, checks its live ViewInfo against the signed bridge config,
and prepares a source-authored physical START report. The report signer is a
separate private Ed25519 seed whose public key must equal the pinned Mini Host
`completionCustodianKey`. The signature covers only the Mini-authored signing
frame. The report and source inputs are fsynced in an owner-private attempt
directory. An error leaves the claim/journal evidence intact. The current
operator plan is then requested through private op44 using only retained BEGIN,
claim ingress, and signed report bytes. Its source inspection must echo the
exact returned plan and all ordered signing slots must match fixed management
key, epoch, role and public-key pins. The operator signs those headers, submits
the source-encoded signatures through op45, and stores the assembled ingress.
An op38 one-shot marker is fsynced before submission. Only a freshly
source-inspected `confirmed/installed` response followed by a repeated physical
MainPID/cgroup check can precede HTTP binding. An uncertain result is never
resubmitted or promoted from op39 historical lookup.

The HTTP listener is **not bound by the public binary**: `spk-hostd` still has
no resident-run command. The staged internal path binds only after the above
confirmed result. Mini commit `24ecf8a` now contains private op44/45 source
and broker allowlist; its matching Linux build and a fresh Store with the
completion custodian and management profile at genesis are still required.
There was no package launch, Mini Store write, or public service in this gate.
A signed physical report alone is not completion.

The supported resident profile requires the exact source image ID
`DREGG/SPK-IMAGE/v1` followed by the signed raw SPK SHA-256, and unit name
`mini-spk-aAPP-gGEN.service`. The physical comparison uses one verified Bread
parse of the retained SPK, not an extracted bridge-config path. An operator
attests to the physical systemd facts; Mini cannot independently observe them.

Linux component verification used the private hbox snapshot
`/tmp/mini-spk-http-response-20260927/native/spk-host`, with only owned files
copied into that snapshot. `CARGO_BUILD_JOBS=2 cargo nextest run --locked
--offline` passed 71/71 tests, and `CARGO_BUILD_JOBS=2 cargo clippy --locked
--offline --all-targets -- -D warnings` passed. The snapshot has earlier pinned
versions of the separately owned `rpc_adapter.rs`, `sandbox.rs`, and
`spawn_gate.rs`; this verdict does not qualify their concurrent shared-tree
edits. The component tests do not constitute a real native lifecycle journey.

Frozen candidate SHA-256s for root review:

| File | SHA-256 |
| --- | --- |
| `native/spk-host/src/completion_native.rs` | `4790c9cbe2016e9a21822f937a516e6d075c40b6c4d38112daa062af4de36cfb` |
| `native/spk-host/src/resident_service.rs` | `b7f42dc772fe65bfd9d669bb4bf445aedd616cb3321671d0e7a424de3a2c2b24` |
| `native/spk-host/src/claim_descriptor.rs` | `2ffcfde37e79797e320442f54854d302aba9f9a17436fe36cb4c3f894305151f` |
| `native/spk-host/src/claim_native.rs` | `fc5eebc9761be989ae791b35a4e5468bd809f1eb72d81f5a8f4bf934c9a23167` |
| `native/spk-host/src/materialize.rs` | `02fb9bdcf65f8decb0b1d3b2d3d23510848ebd1d1f47fda607e386a1ef2eb8a1` |
| `native/spk-host/src/hostd.rs` | `f7d4b1c4cf6a8a66b449edaed177044d958b534cfbb57cdb767684aca52b0e46` |
| `native/spk-host/src/dispatch_native.rs` | `3aaf1ff2ff0412ad8649b1b9366a2a82b5feaa56116513f8320af7bd45cdccd0` |
| `native/spk-host/src/dispatch_author.rs` | `9cce41892a717366bf8b70b7ab676220bb1e30d0dfa11f8d7b3d5a689e3da44f` |
| `native/spk-host/src/http_entrance.rs` | `e6d56b0357ab9c66b43d45bd794ac936c2d737e63ac055e8cfbe1b50f9d34bb3` |
| `native/spk-host/src/lib.rs` | `35e709506f0b4e8dd9d00b3875b53cc7364cd4629a3b78eb51e84cb0e4ac7cb1` |

The source-owned op44 plan derives current management and separate package
observation signing headers; Rust never constructs or accepts those headers
from an HTTP caller. The physical liveness checks are snapshots, not a
continuous lease against later process death or concurrent Mini revocation.
The physical custodian key, management signer pins, exact protected artifact
ancestors, and systemd MainPID are preflighted before one-shot op26, with the
physical checks repeated before the child spawn and at completion.
The first real integrated Store must qualify INSTALL materialization/completion
before START and must support two fixed participants through one resident
RpcDriver; this component gate does not establish that journey.
