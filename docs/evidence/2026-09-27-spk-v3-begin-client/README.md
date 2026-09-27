# Source-bound v3 BEGIN Rust consumer draft — 2026-09-27

`lifecycle_v3_native.rs` is an uncalled shared INSTALL/first-create START
consumer for the source-owned op66/67 plan and assembly. It constructs only
the strict Host request `{kind,clientOperationId,descriptor,createIndex}`
from a `SourceBoundLaunch` made by Mini descriptor authoring against one
signature-verified SPK parse. The client operation ID is a durable local
correlation value; Mini independently derives the signed authorization
operation ID before returning any signing header.

Before signing, Rust compares the source-inspected canonical plan and request
bytes, nested request, v2 launch descriptor and root, installed package root
(also the v2 launch root), fixed app/manifest/management pins, selected
create-action digest, source volume-ID hex shape, and physical unit/image
identity. The source volume ID is not yet compared to the root volume witness;
that exact comparison belongs at the later claim/START physical boundary.
It signs only ordered inspected Ed25519 headers with exact key and epoch pins.
It retains a parent-journal active marker plus one-shot op66, op67 and pre-op22
markers, and accepts only a v3 BEGIN
ingress frame plus a fresh confirmed op22 Outcome. Historical BEGIN-v2 frames
cannot pass the version check. The existing management signer profile is
reused solely as a fixed key-custody profile; no v1 lifecycle ingress fallback
is present.

After a lost reply, a future INSTALL/START caller must inspect and reconcile
the **original** retained ingress and op22 receipt under the active marker.
It must not call `submit_once` with a new attempt directory or client ID.
The generic confirmed Outcome supplies transaction/event identity, but a
claim-v3 source inspector must still prove that receipt belongs to the exact
original event23 ingress before any physical effect. There is no implemented
automatic recovery or physical authorization in this cut.

This module is registered but not called by INSTALL or START. INSTALL-v2
still returns `Unsupported`; `resident_service::run` still refuses before
native or physical work. Source Host op66/67 author/inspector branches were
direct-Lean qualified in the fn review lane, but native event23 receiving,
event24 claim, event25 completion, and their fresh physical-inspection joins
remain outstanding. No Store, SPK child, or resident listener was used.

| Source file | SHA-256 |
| --- | --- |
| `native/spk-host/src/lifecycle_v3_native.rs` | `910149ddb330aba5ce3a2992988c237a6546af667f421ded0137305c4f03c2dc` |
| `native/spk-host/src/install_v3.rs` | `0ff69979f7fdb2ea7a5880abc1012d36f9e7ff8adf73c500064f5a232b8d9fe7` |
| `native/spk-host/src/resident_service.rs` | `b1e85df0bebd53a16256c6215b12cfa349e0c4a0ea4ab74c93e8941b7a651fdf` |
| `native/spk-host/src/resident_launch.rs` | `98aac3d60ac0d6809adc6dfe77f222fe01cffba22519e16418ba6c7e5e822ae2` |
| `native/spk-host/src/lib.rs` | `f59c458d1bdf718e4bd2ba40273d4baf41e9cd040aeae1a990706dfd427f3346` |

The exact source was copied to an isolated hbox target under
`/tank/dregg-build/mini-spk-v3-agent`, run with offline locked dependencies,
two Cargo jobs and a user systemd scope capped at 4 GiB and 200% CPU.
Focused library nextest passed 13/13, including wrong v1 package-root,
request-ID and physical image/unit refusals, plus the exact parent-journal
active-marker collision. Strict all-target Clippy passed.

| Evidence | SHA-256 |
| --- | --- |
| `v3client-r5.log` | `986c1de63b45f0b64983e55acb420942006817f8a6f5ab8d489a1c34f7689fba` |
| `v3client-clippy-r5.log` | `68c2a09e397225ae95b7a3b4b1f40011bc4950643166135578019beeec553072` |
