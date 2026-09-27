# Application share-issue authoring: narrow source gate

This is a bounded Lean source check for the operator-only application share-issue plan and detached assembly route. A third independent Persvati snapshot copied the [op30/31 current-birth narrow image](../2026-09-27-current-application-birth-routes/README.md), then overlaid only `Kernel.ApplicationShareIssueAuthoring` SHA `58282a750e0789439bcea96fc75dd82823ac5bbd8b5302cfcd3ca4e3844c1b06` and `Host.Main` SHA `c931db5dd7cb2291b1a937f0b48123834797b8a7536d063e17179a7e766b0447`.

The [verdict](verdict.log) records both modules compiling serially. Its SHA-256 is `82501cc0c424c77fa7adfbce8061f95b248c7075831964d71cb44bac4cfc118b`; the [two-file source manifest](source-sha256.txt) SHA-256 is `8b14820079671ca0f843337b293c70f6d25455b27c33ac3cd498261494f94837`.

This is a source/OLean gate only. There is no linked native Host, signed share-issue receipt, or participant acceptance from this candidate. The private tree is `/home/ember/build/minidregg-overnight-20260927-shareissue-authoring-narrow`; no live Mini Store was modified.

Operation 32 is operator/custody-private. It calls `prepareLoaded` directly, not `prepareAuthorizedLoaded`, and returns a state-derived **unsigned** signing plan. Participant transport must not expose operation 32 or arbitrary plan requests. Before signing, custody must check the plan headers against its intended spec, subject, and capability. Native receive independently rechecks admission; the plan alone grants no authority.
