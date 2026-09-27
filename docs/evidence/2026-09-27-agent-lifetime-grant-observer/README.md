# Event27 participant observer checkpoint

This source-only follow-up makes the grant participant's read selector part of the canonical event27 grant. The source-derived birth descriptor now includes a third capability: `.observeObject` for that subject on the new grant resource alone. The source rejects reuse of the grant's owner, control, or app-delegation capability IDs. The selector carries the same finite template lifetime as the grant resource's other birth capabilities; it does not authorize app mutation or dispatch. Event26 must additionally check the original issued ticket's current authority, its time and role ceiling, the current grant law and revocation state, and the exact installed grant content root. No event26 receiver, Host route, or native acceptance is claimed by this check.

| Source | SHA-256 |
| --- | --- |
| `Kernel/ApplicationAgentLifetimeGrant.lean` | `d205db30447fb7b917449e7eb6b2a6cb7431000a5ed30414fa72983ff2e3033f` |
| `Kernel/ApplicationAgentLifetimeGrantSource.lean` | `017a94550997167c8901742661d2dbfc7eb9b13634d318f1cbc06ddc26094e32` |

In an isolated hbox overlay at `/tank/dregg-build/mini-lifetime-grant-review-20260927`, these files and the four unchanged lower event27 modules passed the following narrow check in dependency order (exit 0 for all six):

```sh
LEAN_NUM_THREADS=2 lake env lean -o .lake/build/lib/lean/Kernel/<module>.olean Kernel/<module>.lean
```

The modules were `ApplicationAgentLifetimeGrant`, `ApplicationAgentLifetimeGrantSource`, `ApplicationAgentLifetimeGrantDelegation`, `ApplicationAgentLifetimeGrantAtomicBirth`, `ApplicationAgentLifetimeGrantAdmission`, and `ApplicationAgentLifetimeGrantIntentTemplate`. Each compiler log was empty (SHA-256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`). The resulting OLean SHA-256 values, in that order, were `e042da06922afa216b3eb9ceed075407d63396988c32e89991b01bcd2690ad42`, `79d2e32eb773a248e8456227e7c445376ca78ed4b851acf2973511dcdff96c9c`, `597d84d199a13cf2cb23d1a66fc0d22d8ea2e9c1dba40bf4b6f2010e53369057`, `1b4e1cd5331d2dbd4c3649ba18fc2d99a499715dc9127ab3d458c30ffc73b06c`, `b3d86b54ea24e7d157c4e3cbd66d9900c503b7c4b7c993d6fc698dc528807dac`, and `62ede0da900f5cfcd6baa860d689b21007b40eae0a5a03e294e554e6a535d87f`. The base was the exact 55d3868 source and source-qualified prefix-189 manifest SHA-256 `a73745b5e4551ac4817bb392b582b890308b48aff33f45a32f44150ed166e845`. No certified build or shared baseline artifact was changed.
