# STOP v3 Host profile follow-up — source gate

The v3 claim and completion signing plans now use
`ApplicationLifecycleResidentProfile.beginMatchesV3` on their selected BEGIN.
For STOP, that profile checks the prior running unit identity while the Mini
operation generation still advances. Historical v2 authoring continues to use
the unchanged `beginMatches` predicate.

Changed source:

| File | SHA-256 |
| --- | --- |
| `Host/ApplicationLifecycleLaunchClaimAuthoring.lean` | `4a6e7e948cc2815eef67f717aebfcf737ff3eaad708d668fa867eddee274c5e7` |
| `Host/ApplicationLifecycleLaunchCompletionAuthoring.lean` | `a24003c61104701df79b9bf22008abddc3e8b5883f92816e3a91971c403e4887` |

Imported committed STOP lower/BEGIN cut ca277e8:

| File | SHA-256 |
| --- | --- |
| `Kernel/ApplicationLifecycleResidentProfile.lean` | `a2ab7c0e226f6e4071473359b0ffbbb1a5bd2e97522bec4a95d8dc40f14403da` |
| `Kernel/NativeHostReplay.lean` | `21e354bb3e06edf577a00d01100c3db1e0623e6f94993a62cfd5c94433be4385` |
| `Host/ApplicationLifecycleLaunchBeginAuthoring.lean` | `db54362941e3df28a4ee54f19da66a8ff926807c5b14a0ad80e0c44bfdc1772c` |

In an independent writable hbox overlay, source-matched lower OLeans were
copied by value and the two changed Host modules plus `Host.Main` compiled
serially with `LEAN_NUM_THREADS=2`. All three direct Lean commands exited 0
with empty logs. Resulting OLean SHA-256 values are `6f955096...` for claim,
`42a3e54f...` for completion, and `254cb8c8...` for Main. The Main source
remained the committed report-route SHA
`9dbe268baaec650ec0d753258e5b59c91d5a2f6c2622bebb6adb46b43a988c06`.

This is source qualification of the Host checks. No new native binary or
physical STOP was accepted in this gate; the protected host must still observe
the exact prior running unit and submit a signed v2 physical report through
the fresh native completion path.
