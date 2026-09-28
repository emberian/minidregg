# Isolated GitWeb fn recipient bootstrap (2026-09-27)

This is a private recipient deployment on hbox, separate from the retained r3
GitWeb source Store. It contains no selected file atom, release, fn article,
recipient event13, or selected-content ACK. The source remains content resource
8001, owner subject 7/capability 89 in the r3 workroom. This recipient has
domain 8612, empty selected-content target 600 (owner 7/capability 61), and a
separate empty progress target 601 (gateway subject 8/capability 63). The
recipient's subject 7 public enrollment is the exact r3 keyId 7007, epoch 2,
public key `ab328347ea6f8a6db6d9af0fd3b340d62d88455889c0bd4507d73cf125570e37`.
Gateway 8 has an independent private key.

Private retained root:
`/var/lib/minidregg/spk/fixtures/gitweb-fn-recipient-20260927` (0700).
Only the isolated service `mini-gitweb-recipient-r2.service` holds this Store.
Its invocation is `0bd504d15df045b19a86de2cd75c36eb`, Mini binary
SHA-256 `4a9625cfad8f564fd69b1468bdf1114b05f441abc26ec259dff67b68c5d58cec`
(exact committed 18166e5), and Host binary SHA-256
`674e70c22f1e5c7923aa6ef049ead473c959b0551e22f19e0ecbdd48cdf67cca`
(d48aa81). The fn node is the isolated qualified format8 node documented in
[the node evidence](../2026-09-27-fn-preview-node/README.md), with no selected
article POST. Its qualified launcher/core hashes are `432622d2…`/`6e569af1…`.

The first read-only event20 plan refused. Its `namespace-plan/plan.frame`
SHA-256 is `d63201409240e818cd8e0d9081ae47593320f203e4c8f758dd27e8c6d9f05e52`;
no ingress or Store write followed. The old fn pin named the 544-byte fn-host
launcher directly. Host snapshots that executable into a temp directory, where
the launcher cannot find its adjacent `fn-host.core`. A new private absolute
launcher helper retained the qualified image path, its image manifest
(`2d12deb4…`), launcher SHA (`432622d2…`), and core SHA in the certified
manifest (`6e569af1…`). The helper passed a direct read-only position call,
returning the registered cursor SHA `8ffefcd6…`. It does not establish remote
Store completeness; the runtime image remains an operator custody pin.
Helper SHA-256 is `418912989c3f0d33f42b898ddae58977cce20eff7d9fb8547ade1064fa51bdaf`.
The new fn pin/config SHA-256 values are `369d49eb…`/`33d0f1f9…`;
the original pin/config and refused frame remain retained.

One source-owned birth installed target 600 and 601 at Mini accepted count 1.
The wrapper returned 2 because a *later* jq expression was malformed; the
native installed receipt was independently retained, so the birth was never
resent. A corrected, distinct target 600 law-install attempt installed
`eq(request/subject, 7)` at count 2. Signed readbacks show target 600's
current policy address
`96331467673107403990866777949753438772817118828405374221514364637599359657713`,
and target 601's gateway-8 policy address
`50150675285092521471920673721928041931408776656700548997073144630695013237922`.
Both content pages were empty: roots
`4626256791967931348956534661691268091249805547302293488433726010412718534332`
and
`104777879836856975066909071866884970959659064584476547116787816150596634936795`.
The old missing-declaration-nonce install attempt was refused before a call;
it is retained separately.

Fresh event20 registration then passed a local fn status/position check at
ACK 0 and produced a source-owned plan, gateway-8 detached signature,
admitted ingress, and native installed receipt. Retained
`namespace-plan-r2/{plan.bin,ingress.bin,submit.outcome.bin,confirmed.json}`
have SHA-256 respectively `723da059e639144c96b61439f0a347a4db7a729df0c535f61d051a3828786546`,
`3de9bfbfde68a5c106eb7e4f4e06ddba5d119758765381829a21263ec06a6370`,
`8347cb59f9718ba81d434f449c9b07d3eb0acee5ba1237bd9d3572da5e498d3a`,
`b8fd4faf8751c143d456af4459a3d14e290280f5f6cc74c7aace6faf724814dc`.
Receipt: count 3, transaction
`59657770355779778634204086361045104604503360050191537604424961909949258337668`,
event
`32539641155611311013959954590080802348718429867719924761459939914457899090857`,
boundary
`23091923052922126476854248971728545879722714547761965117086235676264508955500`.
Receipt-only event20 lookup passed.

The authenticated empty fn poll was cursor position 2, report and source zero
bytes, from ACK 0. The source-owned event19 plan bound registration count-3
receipt and 0→2; the native submit installed at count 4. Retained
`empty-frontier-plan-r2/{plan.bin,ingress.bin,submit.outcome.bin,confirmed.json}`
SHA-256: `3b188b46952e096fdbee9a76b9197a8290da53dc977523ec490c445cdfe0aa09`,
`6b31a5c2663e7820b7a994ec5fb4fede233bc256eade4d86d1b001646d5dc004`,
`a1d29e1815f33c8baecfba6cc7030e78581b6bef20fe7d9d754b1ba0451277ee`,
`f75bf0f6d44bf137ddf39ff11946aba24671d38e50be5af3f9b08a2bdc096491`.
Receipt: count 4, transaction
`22366741005577295269686278938553562733372072389810169598729960140873695038064`,
event
`24261240902973630558520297333944053984847325138407531819518259001726262946500`,
boundary
`106762430779199336309478123410747105566805350008250207434450273323517486695678`.
Receipt-only event19 lookup passed.

Only after event19 was admitted did the source-owned `fn-empty-page-ack` re-poll
the same empty page, select its verified Mini receipt, and invoke fn ACK.
`empty-ack-r2.json` SHA-256
`e2a1de148226ad6cd086f74f93316fdf772cd43dc1a74016fb812803b9385743`
reports `durable-accepted`, position 2, committed ACK 2. Independent fn
status is ACK 2/frontier 3. The fn ACK itself appended the one neutral event.
No selected-release event17, recipient event13, article, or final readback has
been claimed. The next publication must come from an actual explicitly selected
GitWeb file imported into r3 content 8001 and source-authorized there.
