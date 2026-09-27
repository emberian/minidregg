# Event27 lifetime grant route source gate

This cut adds the missing receiver, historical lookup, detached authoring, and
read-only custody inspection for event27. It has **not** yet been linked through
Host.Main or exercised against a native Store. A plan, inspected JSON, and a
detached signature are not an accepted grant.

The receiver starts from a `NativeHostReplay.Verified` image. A fresh request
uses `deriveVerified`, which selects the original event22 issue in the same
verified history and checks the current source-derived atomic grant birth and
app `.delegateObject` signature before the durable CAS. A confirmed response is
reported only after reloading the Store, verifying its history, and selecting
the original event27 receipt, index, and exact initialized content root.
Receipt-only lookup uses that same selection and never resubmits. A transaction
ID occupied by different ingress is a conflict.

The private authoring plan requires the original event22 in `verified.issues`
and its full accepted record, builds the one-resource birth with the effective
final-payload tariff, and derives both birth and current app signing headers.
Assembly re-prepares the plan against the current verified image and refuses
drift. Native receiving still checks every detached signature and current law.

Direct Lean checks ran in the independent hbox overlay
`/tank/dregg-build/mini-event27-receiver-20260927`, against the committed
Replay source SHA-256 `761a8b25…` and OLean `2a9c158a…`. One bounded
`LEAN_NUM_THREADS=2` compiler held seat2 at a time; the seat was released.
The four checks finished without diagnostics. The final Receiver and Inspector
stdout/stderr logs are retained as empty files in this directory. Lookup and
Authoring passed in the terminal result; no separate stdout/stderr files were
captured for those two. These are direct source checks, not a linked Host or a
native Store run.

| Module | Source SHA-256 | OLean SHA-256 |
| --- | --- | --- |
| `Kernel/ApplicationAgentLifetimeGrantReceiver.lean` | `a5aa2975357669ae0ce1c0b27709df28acd7ed6f068a51543a983ed6a02e023c` | `7e55d25fe17da59dfcf681e4af32849ba45e79779d5d7760c5a24d6130369ffc` |
| `Kernel/ApplicationAgentLifetimeGrantLookup.lean` | `b4b43029b4fcefb199203880404721bd4f352767d81f935f97bab486d2367878` | `d2c2abedd1f2554c68f26015e913ae1941ee188f1d34aa8bd37b25932c5a7f7d` |
| `Host/ApplicationAgentLifetimeGrantAuthoring.lean` | `3e7235bde67e926ad6ead21d56392d2640c6d71d8a3623e87a05ba11a61db972` | `d1e3abcaf59c6bf53bff98b8eef1f5ce06d41d4ba39ddc2f755af50026156289` |
| `Host/ApplicationAgentLifetimeGrantInspection.lean` | `e5dd5cd55b5a3f673732e540527ffe652f2efa7305b6684350d4c198840c0a6a` | `687be78003e4326020b7098d04815b121df51a0a423ce8aecc4c6178626dfdec` |

The final inspector check also projects decoded key ID/epoch, algorithm,
authority root, registry commitment, exact domain/message, and nullifier for
every signing slot. It refuses an undecodable slot and retains the complete
canonical request, funding and finalized birth draft for operator review.

The next gate is a source-qualified Main/Json route at reserved op72–75,
followed by an isolated native event22→event27 fixture with exact lookup and
reply-loss recovery. No existing live Store was changed for this source gate.
