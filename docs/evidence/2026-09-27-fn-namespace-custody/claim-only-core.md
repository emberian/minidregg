# Guarded claim-only durable source gate

This is a narrow Lean source/proof gate for the event20 preflight repair, not a
native Host build or r3 registration success. No fn event module, live Store,
or original r3 attempt was changed.

| Source | SHA-256 | Independent overlay OLean SHA-256 |
| --- | --- | --- |
| `Kernel/DurableCommitProtocol.lean` | `7f06fd2ca87eaed5e6a881176efc566d53ec2d87aa32c8d2998220e738ab8de4` | `bafbbac10ab467ac432d233a23b3db5621a8d653713e8d577ddc6aba9ff070b8` |
| `Kernel/DurableDataIntent.lean` | `832e905da3414df24393ee7618419d88ad32df9b8281bf47a891ef845cb72ddb` | `d54b51808f90f938c054f065a2c1bf5277d0857d549707668269ab43efe5cd59` |
| `Kernel/DurableReceiver.lean` (unchanged) | `f4eade83c8792c0c4b631174485ead84451d680c91cf22aa6415ce3bfe1ebee7` | `5df1d25dc30e9ffdfe7e223a64cc317997e92347f2d3969915c091cd5dfe83cd` |

`LEAN_NUM_THREADS=2 lake env lean Kernel/DurableCommitProtocol.lean -o
/tmp/mini-eventonly-core/Kernel/DurableCommitProtocol.olean` passed. The same
direct `lean -o` check compiled `DurableDataIntent` then `DurableReceiver`
against that independent overlay (overlay first in `LEAN_PATH`). Each exit was
zero and each log was empty, SHA-256
`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
The overlay symlinks unchanged local OLeans; it does not write to the shared
`.lake` directory. No full native link was run.

The [claim-only witness](claim-only-witness.lean), SHA-256
`7c544dcda762df7ffe5a3f96385a976809fb5f21516dbd7c529fe59aed4ca7a5`,
compiled against the overlay with exit zero. Its log at
`/tmp/mini-eventonly-core/witness.log` has SHA-256
`331a7eceec650800b7602dfa70191513bf83f56659266b842688c84b9a745336`.
It specializes the real `DurableReceiver.prepare` and `exactAppend` to a
guarded, one-claim, zero-write intent: prepare is ready, append restores the
accepted snapshot, and a lost-reply retry returns the original recorded
intent. All four witness theorem axiom reports contain only `propext` and
`Quot.sound`.

The core now retains `.noCells` for zero writes **and** zero nullifiers. A
claim-only intent needs a nonempty fresh nullifier and a nonempty read guard
whose root equals the current snapshot. Existing source admission must still
establish the guard's authority meaning; the generic durable executor does
not infer it from arbitrary bytes. Proofs cover funded/fresh readiness,
spent-claim refusal, unchanged roots and canonical cell bytes, exact crash
replay, and the guardless/no-claim/stale-guard negative cases.
