# Qualified fn image with lifted composite bound

Read-only check on 2026-09-26. The existing fn qualification record
[`qual-bbf52159-2026-09-25.md`](/Users/ember/dev/fn/planning/evidence/qual-bbf52159-2026-09-25.md)
names source `bbf52159dcab19228bd6cd0b855b99dd6d68758d`, calls its image
deployable, and records the immutable hbox gate at
`/tank/fn/gates/qual-bbf52159-20260925`. fn's `planning/current-view.json`
also identifies `bbf52159` as the deployed image at the time of this check.

`git merge-base --is-ancestor 4979f0a35 bbf52159` succeeded. The gate's
`books/stx-accept-records.lisp` has SHA-256
`f490e2f78c58c30a852beaa56ad44a12f4a10c5812d81243b4d52144c5e1071c`,
identical to `git show bbf52159:books/stx-accept-records.lisp`. Its line 31
defines `*fn-stxa-max-octets*` as `(- *fn-cbor-max-uint* (+ 9 346))`, so this
qualified source includes the lifted composite bound. The operator's configured
article limit remains a separate constraint.

On hbox, `sha256sum -c image.sha256` in
`/tank/fn/gates/qual-bbf52159-20260925/build/images/bbf52159dcab19228bd6cd0b855b99dd6d68758d`
passed **58 of 58** entries. The manifest includes both relevant cores:

| Image core | SHA-256 |
| --- | --- |
| `fn-host.core` | `6e569af117ba4afcf52bfd74f2a40ac222ead7701bb0b84bac799c53521bfe9e` |
| `fn-host-developer.core` | `e66401023938779925fd97a9b476961dd7f48c6b85e87b9b44b757ded1be79a5` |

These hashes match the qualification record. This check only read the gate and
source history; it did not rebuild, requalify, deploy, or alter a running owner.
