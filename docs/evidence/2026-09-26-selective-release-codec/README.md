# Selective-release codec and pure conflict relation

This is an additive **kernel interface checkpoint**, not a signed receiving
result, private publication, or proof that a claimed source Mini operation was
accepted. `Kernel/FnSelectiveRelease.lean` SHA-256
`97112ffcf4fea9ffdeb21aa8327c1a5e3b297aee8bcf75044f1fd6a48b91b495`
defines a distinct strict framed message. It signs source resource context,
receiver semantics and target, owner policy/key epoch, exact content, nonce,
and audience intent separately from the fn routing group. `recipientOnly`
does not encrypt plaintext. `Kernel/FnSelectiveReleaseProofs.lean` SHA-256
`f6d036bec9927215576f0139517ac2046024f281facf24eee67f62a52208c4a1`
proves all-field byte injectivity consequences and exact-repeat/conflict
classification; a match requires the same complete release and signed call.
This relation does not mint an accepted record or a native signature verdict.

Narrow checks ran in independent warm copy
`/tmp/minidregg-ownr-injection-review`, with the two source files copied from
the hashes above. Each ran one Lean compiler with `LEAN_NUM_THREADS=2`:

```sh
lake env lean Kernel/FnSelectiveRelease.lean \
  -o .lake/build/lib/lean/Kernel/FnSelectiveRelease.olean \
  -i .lake/build/lib/lean/Kernel/FnSelectiveRelease.ilean \
  -c .lake/build/ir/Kernel/FnSelectiveRelease.c --json
lake env lean Kernel/FnSelectiveReleaseProofs.lean \
  -o .lake/build/lib/lean/Kernel/FnSelectiveReleaseProofs.olean \
  -i .lake/build/lib/lean/Kernel/FnSelectiveReleaseProofs.ilean \
  -c .lake/build/ir/Kernel/FnSelectiveReleaseProofs.c --json
```

Both exited zero. Logs:
`/tmp/minidregg-fn-selective-release-narrow.log` SHA-256
`325f4ad2d3a7ecc3368cb8e3df240f4bd2e780bafcb72bc69313a394201c0c2f`;
`/tmp/minidregg-fn-selective-release-proofs-narrow.log` SHA-256
`fb91e9508425c924eb5f20ea3414c0fb27314ee6d961d7a492044b9eb9524c95`.
The proof log's `#print axioms` reports
`[propext, Classical.choice, Quot.sound]` for codec injectivity and
`[propext]` for conflict checks. There are no `sorry` or compiler-only proof
axioms in these results. The only warnings are copied mathlib/batteries
repositories with local changes in the independent warm snapshot.

No recipient current-law resolver, portable owner signature verification,
special ingress, release-key nullifier, native replay branch, or physical
receiving gate is included in this checkpoint. A generic gateway write to
the same content resource must not be interpreted as an authorized release.
Those are required before a receiver may act on this message; the design
boundary is in [FN-SELECTIVE-ORIGIN-PROPOSAL.md](../../FN-SELECTIVE-ORIGIN-PROPOSAL.md).

The next **narrow signature component** is
`Kernel/FnSelectiveReleaseSignature.lean` SHA-256
`4b76ba358968ff2fc487e676a0f1b2e61cdc8e0d1664e1e4f0c660de198ae261`.
It defines a strict versioned owner packet and a private checked constructor.
`verifyNative` selects the current signer key and exact owner-subject target
law from the recipient Mini's complete opened authority, checks the signed
destination and bounded release, checks key epoch/activation/revocation and
expiry, then calls the pinned native Ed25519 verifier over the exact canonical
release preimage. A false, malformed or unavailable native verdict does not
mint `Checked`. This is deliberately a restricted recipient-local owner-law
profile; it does not establish that the claimed source Mini accepted anything,
that fn delivered a trustworthy history, or that `recipientOnly` encrypts
content. It neither admits nor writes a release.

The new module's one-compiler narrow command was:

```sh
lake env lean Kernel/FnSelectiveReleaseSignature.lean \
  -o .lake/build/lib/lean/Kernel/FnSelectiveReleaseSignature.olean \
  -i .lake/build/lib/lean/Kernel/FnSelectiveReleaseSignature.ilean \
  -c .lake/build/ir/Kernel/FnSelectiveReleaseSignature.c --json
```

It exited zero in the same independent warm copy; bounded log
`/tmp/minidregg-fn-selective-signature-narrow.log` SHA-256
`325f4ad2d3a7ecc3368cb8e3df240f4bd2e780bafcb72bc69313a394201c0c2f`
contains only package-local-change warnings. An external importing-module
probe, `Kernel/FnSelectiveReleaseForgeProbe.lean` in that independent copy
(SHA-256 `12cd7bcd04a280f3da4a4465563227eae7d934b1c1a8dfc39ef0a97ba045895f`),
attempted `{ checked with verifier := ... }`; Lean refused with
`constructor for Checked is marked as private`. The probe log is
`/tmp/minidregg-fn-selective-forge-probe.log` SHA-256
`32cae188cabafe5ffbefca80d5733ac9275af7b882202af952ad0ed79c0fc84b`.
This tests that particular record-update route; it is not a cryptographic or
physical receiving gate. A separate source-owned ingress, capability admission,
durable nullifier and replay variant are still required.
