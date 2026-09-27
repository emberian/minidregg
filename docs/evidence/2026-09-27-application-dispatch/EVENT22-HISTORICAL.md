# Event22 historical share-issue dispatch evidence

This is a narrow source-qualified Lean gate for the distinct grain-backed
share-issue event22. It is not a native Host link, an accepted physical issue,
or an SPK delivery test. The committed event22 Source/Admission/Receiver inputs
are from `d631d26` (source SHA-256 prefixes `e543bf37`, `ace43f67`,
`0eb50dcd`); their source-matched OLeans were copied from
`/tmp/mini-share-grain-source-20260927/Kernel` into the independent writable
overlay `/home/ember/build/minidregg-event21-lower-check/lib/Kernel`.

`IssuedEvidence` has a private constructor and two separate admitted-source
proof branches. The event15 factory still requires its native accepted issue
and complete original intent-record equality. The new event22 factory requires
the joint grain-backed accepted issue and equality to its complete event22
intent. Shared `spec`, canonical issue ingress bytes, descriptor and record
are thus derived from one branch, not caller assertions. Dispatch checks the
exact issue ingress bytes and current app/ticket/grants against these fields.

Replay decodes the event22 frame before ordinary grain birth, calls its native
joint admission at the original prefix, and retains the new issue certificate
only after complete record matching, durable advance, and post-image
validation in the same replay walk. Warm human and agent dispatch use that
chronological certificate. The old event15 branch is unchanged.

| Changed module | Source SHA-256 | Matching OLean SHA-256 |
| --- | --- | --- |
| `Kernel/ApplicationDispatchHistoricalCore.lean` | `69077487d1c9592013131e38f5c2b7bd7ca43ca4b426e7d501ea10f0fb90da05` | `750dfb5998383ee47a10fa1ef5c8fef8435d2120a537774878feee3656457857` |
| `Kernel/NativeHostReplay.lean` | `ad900b5a2f28ec97c1f6638d556637147f184dd492d54625a6fd2fef3574bf14` | `f78fdc8817f2efcb4aebc175c6a454ca97e19123f5f7be36c3a3d2a6f3c20e8e` |
| `Kernel/ApplicationDispatchAgentCore.lean` | `a820e486ce2e2501cfb3c77314e5fb2bb960533fcfc65df8d264f72d658fb703` | `d9ebac7b69c16c04584fc54b02907f6893978186d6febe1a8f100f46af1e8810` |
| `Kernel/ApplicationDispatchProjection.lean` | `b124b16bdccd4ef2985107a5245bdab61701d79603593347adbbefc606b38a43` | `5f7a4500636fba17bbf7b202285439e5596b02237726b984b742aff2cd4fc982` |
| `Kernel/ApplicationDispatchAuthoring.lean` | `cfff2770fd52972869c71e890d23f9f2669afbff9317028ebcd2c62962e5ac7e` | `1db758b37bb555919e2ce395a3c57b61673137beb040d0e76ecf501df54336b1` |
| `Kernel/ApplicationDispatchAgentAuthoring.lean` | `1d30340c3281f9c170e8c41c143492e4e2940f62a6ecf10bd13c35a4f71dc2fc` | `0e7de1a6d16541dac39b2876787d1d3d54b442b47aab8635b17b4df783423ca8` |
| `Kernel/ApplicationDispatchAgentPaidAuthoring.lean` | `86bc5bf219fdf0b2ad91e35bf6b2ec38d2addd4f4e10e01123c6bfa19d89608c` | `17e5ad98d316495c80352f8794dabb8d1a556e46e02d70a086016692f3434b3c` |

Every source file above was copied byte-identically into the independent
overlay before its direct Lean check. The serial order was HistoricalCore,
AgentCore, Replay, ApplicationShareIssueHistorical, Projection,
AgentProjection, AgentReceiver, AgentLookup, Authoring, AgentAuthoring,
PaidAuthoring, then Upper, human Receiver and human Lookup; all passed.
The separately present `ApplicationDispatchAgentReserve.lean` is an untracked
older draft with a missing `ApplicationDispatchAgentPurse` import and is not
in the event21/e22 route or this qualified closure.

The exact direct-check command, run from the overlay and repeated with only
the module name changed, was:

```sh
base_path=$(cd /home/ember/build/minidregg-overnight-20260927-completion-next && /home/ember/.elan/bin/lake env printenv LEAN_PATH)
LEAN_PATH="$PWD/lib:$base_path" LEAN_NUM_THREADS=2 /home/ember/.elan/bin/lean Kernel/NativeHostReplay.lean -o lib/Kernel/NativeHostReplay.olean
```

The final Replay check output is
[`NativeHostReplay-event22-final.log`](NativeHostReplay-event22-final.log),
SHA-256 `3466e88f21218fe7c070c50a9908a0d67b1b5c726a8280006163c771fdbcd1e3`.
It reports the existing permitted axiom dependencies and no errors.
The disjoint receipt-only op55 helper
`Kernel/ApplicationShareIssueGrainLookup.lean` at source SHA-256
`e57eb27f49fc22795cb4ecd63c2d5018316043ff61e27bfa6db071c2ef432989`
and OLean SHA-256 `7fba8980089c55a9a41c0578e407ff00d4e88cc2ebe86b3d0df417e2f54abcc0`
also passed direct Lean against the Replay/OLean pair above. Host Main54–57
source/OLean pair `141ff6cdbe856df9263afa5d718c1527cc5a87150b91081afb385b317b6893c5` /
`aaa8fd9eeaa307f5475361cd6fae35473fdcf9d9eda14288d1b73911521224ba`
passed in the separate `/tmp/minidregg-agent-main-check` overlay. The helper re-admits
event22 on the verifier-selected original prefix and compares the complete
record and exact receipt; it cannot mint a delivery permit. A real native
event22 fixture remains a separate gate.
