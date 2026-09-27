# Event27 lower admission checkpoint

This is a source-only component cut following the committed lifetime-grant codec at `9cdf401`. It has no Host route, no native event27 submit, and no historical ticket certificate. The new `IntentTemplate.template` is deterministic intent data; a future upper Replay admission must require a verifier-minted original event22 issue before using it.

| File | SHA-256 |
| --- | --- |
| `Kernel/ApplicationAgentLifetimeGrantSource.lean` (domain-bound event ID follow-up) | `b51df9c18ff5393143281282be2ccde3433b11e6e0c2846bcf812224b7b85c1b` |
| `Kernel/ApplicationAgentLifetimeGrantDelegation.lean` | `da7439f0bf27e048752616276d844f9ba1debbd00a77d0b73f78caadb46761f2` |
| `Kernel/ApplicationAgentLifetimeGrantAtomicBirth.lean` | `38d82e9324bfa7337df821a5888e2615ce2ec46206416b6999830e2fefc570e1` |
| `Kernel/ApplicationAgentLifetimeGrantAdmission.lean` | `5fcd184b70b5947b26435ce3399747c340672b073db550b3d4bdd6aa06acf323` |
| `Kernel/ApplicationAgentLifetimeGrantIntentTemplate.lean` | `67e62e0edb4b30fd16acb90c64a46bc45c4c1b7731ce057d2d6e723edfb3e4fe` |

Each file passed `LEAN_NUM_THREADS=2 lake env lean -o .lake/build/lib/lean/Kernel/<module>.olean Kernel/<module>.lean` in dependency order, exit 0, with empty compiler output (SHA-256 of each log: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`). The isolated hbox overlay is `/tank/dregg-build/mini-lifetime-grant-review-20260927`; it uses the exact 55d3868 source tar and source-qualified prefix-189 manifest SHA-256 `a73745b5e4551ac4817bb392b582b890308b48aff33f45a32f44150ed166e845`. No certified build or shared baseline was modified.

The lower admission checks a source-derived final-payload tariff and complete born descriptor against native birth admission; separately, it checks a current signed `.delegateObject` authorization on the same loaded image. The atomic-birth component substitutes only the checked final grant atom for the fresh empty birth cell, preserving write IDs, pre-root, other writes, read guards and root-bound post bytes. The intent template retains both one-use birth/issue nullifiers, all native birth guards, the current app read guard, exact charge and domain-bound event27 bytes. It cannot prove original event22 provenance on its own.
