# Event26 source receiver and recovery lookup

This is a source-only cut. The event26 receiver requires a Replay-minted
historical event22 ticket, event27 grant, and original v3-bound purse reserve,
then current app/session/parent/purse/grant admission. It emits a delivery
permit only when its own physical CAS reports `.installed`, the complete
post-image reads back exactly, and `validateLoaded` accepts it. An
`.alreadyPresent` or uncertain CAS response may confirm exact history but
cannot mint another delivery permit; the separate lookup returns only the
historical receipt. The permit checks the physical tip again at handoff.

The versioned paid projection retains the original event22 issue index,
four-field receipt and encoded birth descriptor; event27 issue receipt,
certified initialized grant root and current full grant root; exact v3 grant
context and reserve nonce; original reserve index/receipt; and fresh signed
app/session, parent and purse coordinates. The app session's original parent
generation remains provenance, while the current parent generation is a
separate physical fence. This is not a Host op or runtime delivery path yet.

`ApplicationDispatchAuthoring.prepareWithParent` still applies the old
original-generation check before any signing headers are prepared. Its body
is factored into a private helper. A distinct source-owned lifetime wrapper
selects the certified grant from the same verified walk and a current reserved
parent before calling that helper. The old event21 request/plan codecs and
source authoring behavior are unchanged. A full event26 reserve/paid author
plan and Host route remain separate work.

## Narrow source check

The independent hbox overlay
`/tank/dregg-build/mini-lifetime-grant-review-20260927` imports the immutable
exact-55d3868 prefix-292 (manifest SHA-256
`0c0b8fd0aedf4f97650d3ad4d369629e955943fd472c0ec089eb4de0f017d1cd`).
It was updated with source-qualified `NativeHostContext.olean`
`b91b81024553f1644d94393d69f94226d3a882669df5a7f66451f83612065e81`,
event26 `NativeHostReplay.olean`
`2a9c158a5e62cc9c55cc93126aa02961ceab26c9e91a973b17c9d7b53d5a569f`
(source SHA-256
`761a8b2594a44153d876a7efae6a830f632c4b6ff878d211e1f3eed7c40fe429`), and fresh-CAS `DurableReceiverIO.olean`
`2fbf265250a6abcea1b4106ecd87858215e1e708cc024786e959af240d47efda`
(source SHA-256 `6f13945cd93146e7cf9cbf078641dd57a1a8e14051f323aaf0010e12561e2673`). The Replay and Compiler source cuts belong to
their respective owners; this evidence does not certify a native linked Host.

The following four commands ran serially under an atomically claimed seat,
with `LEAN_NUM_THREADS=2` and `lake env lean -o
.lake/build/lib/lean/Kernel/<module>.olean Kernel/<module>.lean`.
All exited 0 and their individual captured compiler logs are empty (SHA-256
`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`).
The seat was released by an EXIT trap.
The eight source/log paths are verified by [SHA256SUMS](SHA256SUMS) from the
repository root (`shasum -a 256 -c ...`: 8/8 OK).

| Kernel module | Source SHA-256 | OLean SHA-256 |
| --- | --- | --- |
| ApplicationDispatchAuthoring | `3b7c5add827801f3009c02907503d9b4ef5a2a896e2c7c74d772a7f18221b4c2` | `c08bf4cfe196d8fb9ea33c3287206cfefdbc8329e449fc2d4f3eafe84d049371` |
| ApplicationAgentLifetimeDispatchProjection | `9cb0c98061f3bc7664d36385a0177dc9aed512cb2683dfba6b988f222918645f` | `944f251492f4fcfee00d91d76c9e58ca5d7b84426476335de1913b1a8f0ada83` |
| ApplicationAgentLifetimeDispatchLookup | `f67cd335a79c0225a9968cc99046f4b7fa50259f2cd78f48e114627a747e05cf` | `ac6fbecea971ebc6f12180c54b5944d3daa1c933da84e4e064c721eae9e24004` |
| ApplicationAgentLifetimeDispatchReceiver | `796c755e29180a30d4be2218b14b3beeb0b93b9e53c52d250e6fd2317086b2f7` | `8334c93924ea8e9570b68a169c5dc073af9f91082ad55f70c0c0411e02938920` |
