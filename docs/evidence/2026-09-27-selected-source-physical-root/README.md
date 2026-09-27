# Selected source physical-root refusal and repair

The first isolated selected-source publisher attempt stopped in the native
`selected-release-source-plan` step, before an ingress existed. The source Host
was the qualified Linux source-check image SHA-256
`69cf81ae5d40118fe9d009559ea7d8e04753c6299924d560d3f03768296cf6f3`.
The private source Store and packet are retained at
`/tmp/mini-selected-source-qualified-20260927/evidence-r1` on Persvati. Its
403-byte owner packet has SHA-256
`0ce9aa1c59ba8014bfbec7acbe4a4adea276f29c852ddb74298805b29dc8810c`;
the 840-byte authored article has SHA-256
`158eee4081392d5a89e9ba4db0050022308181b8aa1f0f57c78d98e2b2ac2123`
and a fresh signed Message-ID. The publisher run log is
`/tmp/mini-selected-source-qualified-20260927/source-publish-r1.run.log`,
SHA-256 `9615a2a8d91e12621d98b2df176b70b1a7b2a8bc09fd16264ed8ede164ccffa2`.
No source op24/25, fn POST, or recipient op20 occurred in this attempt.

A bounded read-only Lean probe reopened that exact Store using the qualified
source closure; retained private log
`/tmp/minidregg-selected-source-preconditions.log` has SHA-256
`f3f6af718c247f2853510e7ab386c4ab33aa62cf678b72185bf16cc7a9638af6`.
Its output was:

| Check | Result |
| --- | --- |
| Owner packet signature length | 64 bytes |
| Selected public content length | 47 bytes |
| Source domain and semantics equal pinned source config | true / true |
| Public-peerable and bounded release | true / true |
| Signed source parent equals loaded directory's content-page root | true |
| Signed source parent equals durable physical-cell root | false |
| Loaded directory's content-page root equals durable physical-cell root | false |

The last two differences are expected: the packet binds the **inner content
version**, while durable CAS guards the **outer encoded physical cell**. The
old `FnSelectiveReleaseSourceAuthority.prepare` incorrectly required those
distinct roots to be equal, causing the generic refusal.

The repair retains exact inner-root and selected-atom checks. New
`Kernel/PhysicalResourceReadGuard.lean` proves the outer root current from the
verifier-loaded directory bytes and durable snapshot coherence; the source
authorization event uses that outer root in its read guard. The new helper
SHA-256 is `2c447ebbd5846308eab23486c59a235352343343477ce4f227c9589945334f8d`;
repaired source authority SHA-256 is
`c948b6be3608625c2876cb628e4f76f0f49ae327fd7e2cd5c9ee02143ca90fe4`.
A private narrow `lake build Kernel.FnSelectiveReleaseSourceReceiver` passed;
The captured [build log](build.log) preserves that check, including the existing
dependency linter output and final successful build verdict.

This source check is not native acceptance. A source-matched linked Host must
rerun the unchanged private candidate and confirm the source event, exact
lookup, and protected POST before recipient delivery is claimed.
