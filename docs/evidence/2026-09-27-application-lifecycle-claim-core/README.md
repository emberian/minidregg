# Conditional lifecycle claim core

This checkpoint contains source-only preparation for a one-shot Mini lifecycle claim. It does **not** publish an op26/27 route, commit a claim, attest a host process, or authorize launch.

The historical leg selects the exact accepted-record index from a physically loaded image, reconstructs its prior prefix, re-admits the original signed lifecycle BEGIN at that prefix's logical height, and compares the complete source-derived `IntentRecord`. The current leg checks the original BEGIN subject and mutation capability through current DRC admission, the installed v2 management law, physical target shape, exact pending app state and image boundary, and separate signed app/package observations on one loaded image. The derived special intent retains the DRC writes, adds event and nullifier version 16, and adds the independent package read guard.

The app observation reads the app cell that the claim writes. Requiring it to be an additional read-only guard would reject every legitimate claim; the DRC target's expected pre-root and physical shape guard that write. The package observation is on a separate read-only cell and contributes the extra guard. Two observation incidences and their proof/memory costs are charged; the special ingress and nullifier are charged by the source tariff. No physical host effect is charged.

The three frozen files are:

| File | SHA-256 |
| --- | --- |
| `Kernel/ApplicationLifecycleClaimHistory.lean` | `3cd6a2afac7305e2baee139352cee31193b03e771903397b4b3c5360229db259` |
| `Kernel/ApplicationLifecycleClaimCurrent.lean` | `f2fd76014e6f9837b83fc7af7a142c1d80ef7cae6a3e62fe9791ab5edc9c5e2f` |
| `Kernel/ApplicationLifecycleClaimCore.lean` | `fc80dc9dd1f8c11bbed25cd57e03dd1da9001184d489696c3694c30d3ed4f952` |

`LEAN_NUM_THREADS=2 lake build Kernel.ApplicationLifecycleClaimHistory Kernel.ApplicationLifecycleClaimCurrent Kernel.ApplicationLifecycleClaimCore` passed (3108 jobs) in independent warm snapshot `/tmp/minidregg-lifecycle-begin-20260927`. The captured [build log](claim-core-final.log) has SHA-256 `396c54fb11342b69b0aa5bb59764af1b2938c30ffccad19cd7ad4c2bd67d9e7e`.

Before a host can consume a claim, a single replay pass must return an executable selected original prefix tied to its admitted prior trace and the exact verified tip. An upper receiver must then submit the conditional intent against that verified tip and require exact post-CAS readback; a historical or concurrently suffixed confirmation is receipt-only. No lower candidate or generic DRC receipt is a launch permit.
