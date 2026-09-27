# Fresh signed grain-backed content birth

This is one isolated Persvati Store, distinct from failed r1/r2 and every
hosted workroom Store. The source-matched Linux Host was SHA-256
`30731bb4e35b784ab58fa8f442407ef2bc4fddeed77ab782a5056f107096fc82`
(Host.Json `31f400a1`, Host.Main `d5daf1d7`, 181-module guarded suffix/link
PASS). Its source manifest was SHA-256
`6a819c8125c5c78031b438beb4592281781b0c974d5338250e06514f0757e7ea`.
The original runner source was SHA-256 `f056be2bc2096aa6fa0e931e40e634c3bcd9532a3d3a9af4e891f229826acf59`.

The signed composite call installed content resource **8301** at accepted
count **11**. The signed resource view has document 8301 and no entries.
The tool grain 7902 then had generation 1, remaining 47, reserved 0 and
status 1; the parent 7901 retained generation 1, remaining 99, reserved 1
and status 3. The same-profile owner 7 bare content birth installed resource
8303 at accepted count **12**, with a signed empty content view. The attached
`call.bin`, outcomes, challenges, views, and signed observations are retained
under their corresponding directories.

The original runner exited 1 **after** both accepted births. Its final
assertion expected an internal factory-policy refusal for worker 8's bare
birth of resource 8302. The actual public outcome was the native uniform
`admission` / `request refused`; `NativeHost.publicSubmissionOutcome` erases
all internal submission-refusal reasons. The retained worker call has a
nonempty plan and signed call. Its internal rejection reason cannot be
deduced from the public outcome alone.

The separate `verify-r3-negative.sh` read-only check (source SHA-256
`7a9b922f86a7d65e7a8cf5796680be35126df643d4904c2d1a494ad79daae00c`)
checked those retained artifacts, then made a **new
signed read**, without repeating either birth or the refused write. The
signed image boundary after refusal exactly equaled the one observed just
before it: `31064171762746748538425331557789061745044183474145812816010729387751170303122`.
That check printed `retained worker bare refusal and unchanged signed image
PASS`; its private log SHA-256 is
`9b0a1682bca473dd45e15bf448b0a08491ba0532519b5c961609e4f8a081b86e`.

`scripts/probe-grain-birth-factory-law.lean` (source SHA-256
`5d2dcb32fd06784fbb34b8bba8716036ef3a8b5a15e206da6a3ec773efb5a8e3`)
proves for every policy state
that the installed fixture predicate refuses a subject-8 bare factory
mutation when the grain-backed mode slot is absent, while allowing owner 7
and subject 8 with the mode slot. It compiled with axiom report `[propext]`
only (private narrow log SHA-256
`c5a5beebf774991cfc38308257c8331671503be7046b1cc295769230428e28c3`).
The source predicate and retained genesis were checked for exact equality
by the original runner. This policy proof and the uniform native refusal
are distinct claims.

No private keys, live config, Store, or complete host transcript are copied
here. This is native Mini acceptance; no Hermes MCP resource birth is claimed.
