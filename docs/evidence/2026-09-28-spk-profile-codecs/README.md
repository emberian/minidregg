# Signed SPK API profile codec proof — 2026-09-28

`Kernel/ApplicationSpkProfileProofs.lean` passed a direct Lean 4.30 source check
in an independent Persvati scratch overlay. The checked source SHA-256 was
`0cb0b012c6ffa8ac83fd6dbfed8cdaa5990ab6eb7262c74c8be7c013f8b886a0`;
the imported package and launch sources were respectively
`982982dca5c7aa696164c420305a0cd25a2d6e82cc4d6bcb8781840f24814373`
and `98111517e43621c7ff416c1931e1dd5031b9aa565a89bf30d99fda5fbba458eb`.
The scratch library came from the independently qualified 272 warm Mini root,
with the source-matched 579 enrollment imports and the two current SPK OLeans.
The proof check used one leased Lean seat and `LEAN_NUM_THREADS=2`; the seat
was released. [The captured Lean output](proof-axioms.log) has SHA-256
`eb4d6cc3dd70c2ce1330d8c51eefac9ab25e7347f97890c0442a1dc47d1b77fe`.

The source maps a web-only or exact signed `/repo.git/` path to the original
package v1 and launch v2 frames and roots. Any other admitted signed API
prefix, including `/`, uses package v2 and launch v3 frames and roots. The
prefix is a literal slash-terminated ASCII byte path of at most 256 bytes;
interior segments are nonempty `[A-Za-z0-9._~-]` except `.` and `..`.
Percent escapes and normalization are not part of this grammar. The native
`signed-api-path` crate uses the same bounds and segment rule.

The proof module establishes general selected-profile encode/decode
roundtrip, decoded canonical bytes, and canonical-byte injectivity for both
descriptors. The canonical decoder also refuses a new-profile descriptor
carried in a legacy frame. Four **finite frame comparisons** use `native_decide` because
Lean 4.30 does not kernel-reduce `String.toUTF8`. `#print axioms` in the
captured log exposes one named compiler axiom for each comparison, alongside
ordinary `propext` (and `Classical.choice`/`Quot.sound` in the injectivity
theorems). The general claims are therefore compiler-dependent at precisely
those four finite literal comparisons; this check is a source proof, not a
native admission or deployment result.
