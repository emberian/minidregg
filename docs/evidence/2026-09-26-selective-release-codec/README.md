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
