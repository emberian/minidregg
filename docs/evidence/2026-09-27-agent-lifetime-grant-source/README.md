# Agent lifetime grant source checkpoint

This is an additive source-only checkpoint against Mini commit `d513bfadfa63337ceede0663dc9c542fe53ebaa1`. It defines the canonical grant record and the source-authored event27 issue draft. It does **not** admit or durably install event27, verify the historical ticket receipt, expose a Host operation, or authorize event26 dispatch.

| File | SHA-256 |
| --- | --- |
| `Kernel/ApplicationAgentLifetimeGrant.lean` | `a85e6665196527b0433891412300e7059396d13abd9caf11205ec8cd70b028bb` |
| `Kernel/ApplicationAgentLifetimeGrantSource.lean` | `8f25c57ff9d590b247440dfcd13f6fe1c931a84ed60e324b95b9ece6569ced14` |

Both files passed narrow checks in the isolated hbox overlay `/tank/dregg-build/mini-lifetime-grant-review-20260927`, extracted from the exact 55d3868 source tar. The overlay copied the source-qualified prefix-189 Lean artifacts; `/tank/dregg-build/minidregg-55d3868-evidence/prefix-189/manifest.json` has SHA-256 `a73745b5e4551ac4817bb392b582b890308b48aff33f45a32f44150ed166e845`. The final commands, from the overlay root, were:

```sh
LEAN_NUM_THREADS=2 lake env lean -o .lake/build/lib/lean/Kernel/ApplicationAgentLifetimeGrant.olean Kernel/ApplicationAgentLifetimeGrant.lean > grant.log 2>&1
LEAN_NUM_THREADS=2 lake env lean -o .lake/build/lib/lean/Kernel/ApplicationAgentLifetimeGrantSource.olean Kernel/ApplicationAgentLifetimeGrantSource.lean > source.log 2>&1
```

Each command returned exit 0, recorded in [narrow-verdict.txt](narrow-verdict.txt). Both final compiler logs are empty (SHA-256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`). Resulting isolated OLeans are `58e93b972fde19146781a3ce64d5f07128e0650bc55260b8ab17ea6abd34bfdc` and `174b80ffe9c61d87d6366216d9d4c3b0cfe90b13b673494f2367a2eb90c3ac33` respectively. The certified prefix and active builder were not changed. No `sorry` or `admit` tactic occurs in these files.

The grant keeps the original ticket receipt/index and original parent generation as issuance provenance. The source computes an exact `.delegateObject` request, one content-resource birth with an empty initial cell, the final grant atom, two derived capabilities, and a fee quote for the final payload. Only a future event27 receiver can join those pieces on one verified image, compare the complete descriptor, and install the final atom atomically. Event26 must independently replay that issuance at its authenticated prefix and check current grant content, current law and capability, and a fresh parent/purse witness; changing the current law is not by itself a revocation.
