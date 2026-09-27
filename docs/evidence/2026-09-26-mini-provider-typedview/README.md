# Mini typed fn inbox native checkpoint (2026-09-27 UTC)

These independent Mac and Linux snapshots add only the committed `6828c7f`
`Host/FnInboxView.lean` (SHA-256
`7c2f69f9c34a521b0ce0ea32eefc3fd2a741240ef60bc7cc35128610887afe7b`)
to the [provider-metering source closure](../2026-09-26-mini-provider-metering/README.md).
That base deliberately pins the earlier `Kernel/ResourceBirthController.lean`
blob; these images therefore do not claim to be the entire `6828c7f` tree.
The 171-module source manifests are byte-identical across platforms. Their
diff against the provider-metering manifests contains exactly the one typed-view
module. No running Host or Store was replaced.

The guarded incremental builder verified the baseline source, package, and
artifact provenance, then compiled modules 165–171 and linked 3,104 response
objects. Both builds reverified all 171 source and four output artifact hashes.
The no-argument `usage_exit=1` is expected.

- Mac arm64: `/tmp/minidregg-overnight-20260926/minidregg-host-provider-typedview`,
  SHA-256 `8e24573962ec54d81ecd6859dc2dd5b8158610f926401aa903a1ec6eb4ba7524`;
  [manifest](mac-manifest.txt), [source hashes](mac-source-sha256.txt),
  [artifact hashes](mac-artifact-sha256.txt), and [closure](mac-source-modules.txt).
- Linux x86-64: `/home/ember/build/minidregg-overnight-20260926/evidence/minidregg-host-provider-typedview`,
  SHA-256 `454b06489e9f1787124c91e881eeced9b3b95c0ece81c69a4113e67d3461e2de`;
  [manifest](linux-manifest.txt), [source hashes](linux-source-sha256.txt),
  [artifact hashes](linux-artifact-sha256.txt), and [closure](linux-source-modules.txt).

This is a build and source checkpoint. The signed A view presentation is a
separate runtime check. No private Store, key, request, or executable is copied
into this directory.
