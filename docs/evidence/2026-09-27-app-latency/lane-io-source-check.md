# Proved lane IO replacement

Source SHA-256 for `Compiler/Sp800185Cshake256Core.lean`:
`9810ddac1911c0126c9558d15af61557f60080cf2e7da146ce856543daf616c9`.

The new `laneFromBlock_eqUInt64` and `stateByte_eqUInt64` are general
equalities used by `@[csimp]`, not tests of chosen messages. They cover short
blocks with zero-filled missing bytes and every state/index. Narrow Lean
checking and C generation exited zero. Each theorem's reported axioms were
`[propext, Quot.sound]`; neither uses `sorry` or compiled decision axioms.
The previous UInt64 permutation implementation is unchanged.

The generated C SHA-256 was
`7fa5dce858548dc10a21cf4597c2f71ef39333c407af613c8187342302861f25`.
Its lane input/output replacements use UInt64 shift/XOR/conversion operations,
and their production callers select the substituted definitions. Compiling
that generated C with `lake env leanc -c` also exited zero. Root inspected the
source diff, the two axiom lines, C-generation log and generated symbols.

Temporary artifacts were `/tmp/mini-lane-core-narrow.log`,
`/tmp/mini-lane-core-c.log`, `/tmp/mini-lane-core.c`, and
`/tmp/mini-lane-core-cc.log`. This record does not claim an end-to-end latency
improvement or a newly linked Host. A native hash microbenchmark and exact
copied-Store before/after check remain required for performance claims.
