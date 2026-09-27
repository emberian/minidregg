# r3 event20 native refusal diagnosis

This is a bounded, read-only diagnosis of the original r3 attempt. It does not
turn the refused op40 into an accepted registration or authorize a resend. The
qualified Linux Host was `bf04c29`, SHA-256
`cf931aae46102755a97920feed13afa36c83ef4d1bfabd2fb17dee1c8bbfa943`.
The retained 799-byte ingress at
`/tmp/mini-selected-fn-recipient-20260927-3/namespace-attempt-1/ingress.bin`
has SHA-256 `31b1619cbe22e7101f2863c9e753b02f230948ee867588890577c8e2c5f3befe`;
the source-owned plan has SHA-256
`844a6f0a50234439036f953903431bc5b293ff1b2ed52deb32d138db4a55d5ce`.
The original op40 typed outcome was `refused` at admission, and op41 returned
`absent`. No op40 was sent by the diagnostic.

The diagnostic imported the exact build's compiled modules from
`/home/ember/build/minidregg-overnight-20260927-claim-next` and read the
retained ingress and current Store. Its private script is
`/tmp/mini-event20-r3-readonly-diag.lean` (SHA-256
`baa1c5afcdd71053186eceb4811edaa6d76004e6ea4d4d59074c29a1b7bca7bb`);
its selected, keyless log is SHA-256
`46beeb49bd8d6480f72e34f66774f5ee5f3f5fdeb301dc4461930dadb74f8ef8`:

```text
ingress decoded
opened
verified
namespace absent: true
legacy: true error: false
law pin: true
gateway prepared: true
admit: ok
durable prepare rejected: Minidregg.Kernel.DurableDataIntent.RejectReason.durable (Minidregg.Kernel.DurableCommitProtocol.RejectReason.noCells)
```

Here `legacy: true error: false` means `frontierLegacyFor` returned `.ok
none`: the outer `Option` is present and contains no legacy anchor. Native
gateway signature and current policy admission passed in
`FnConsumerNamespaceAdmission.admitVerified`; the failure is the subsequent
durable preflight, before CAS. In the certified source,
`Kernel/FnConsumerNamespaceAdmissionAt.lean` SHA-256
`62257c2bfb4b262a42888a3df5c5751939689b284e34815e62993d995d7c757d`
constructs the event20 intent with `writes := []`, a current gateway read
guard, authority guards, one namespace nullifier, charge and event.
`Kernel/DurableCommitProtocol.lean` SHA-256
`c7e2c80cb235be701e3a69208956eb6599ef8b01a5881c67388e1cf5f70ee891`
rejects every empty `rootWrites` list as `.noCells` in `Intent.preflight`.

The appropriate repair is a separately reviewed durable law for a guarded,
one-use nullifier-only registration. A dummy gateway-content write would
change the source contract. The diagnosis establishes this exact pre-CAS
rejection; it is not a native acceptance result for any later source change.
