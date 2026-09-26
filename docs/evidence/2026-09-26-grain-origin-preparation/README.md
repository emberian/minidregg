# Guarded verified grain R preparation (2026-09-26)

`Host/GrainOriginPreparation.lean` SHA-256
`1e299497956ff0874ba7ed15539c2a0863beff80f94dc780e4f3b129c8aef6e7`
typechecked in the isolated `/tmp/minidregg-overnight-20260926-grain-origin`
snapshot. The focused probe `scripts/probe-grain-origin-preparation.lean`
SHA-256 `8410e4cb7b43e07ca0f3f813943336235adc02f4f8c49504b17d7e1fba38b9c3`
ran with `LEAN_NUM_THREADS=2 lake env lean scripts/probe-grain-origin-preparation.lean`
and exited 0. Its emitted result is [verified-r.log](verified-r.log).

The probe loaded the independent origin pin and the recorded accepted
[`7003-package.bin`](../2026-09-26-hermes-grain-origin/7003-package.bin),
called native `FnEvidence.verify` through the new guarded helper, then
compared the rendered bytes with the exact recorded
[`R.source`](../2026-09-26-hermes-grain-origin/R.source). It confirmed
191,283 source bytes, an accepted prefix of 135,546 bytes through receipt
count 10, and rejected missing whole-prefix intent or a destination group
different from the authored article. Domain-separated cSHAKE256 identifiers
for the complete package and accepted-prefix byte strings were respectively:

```text
package 0d982c02f484ffbbaa5591bf1d786d6262f9d74a00dca7e9093424e89eccaff7
prefix  46fe10e99edaa3ddf4f47eedbf7f0222dc3d82f8e25313f6ff99ef344ecff98d
```

This is a read-only preparation check. The operator's disclosure intent
records a request to render the full-prefix article; it is not proof of
contributors' consent, a recipient restriction after fn peering, or
authorization to sign or publish the article. No fn transport was invoked.

The reusable operator command takes an independently selected origin config,
strict [request-r5.json](request-r5.json), exact package and a **new** output
directory:

```text
minidregg-host ORIGIN-CONFIG.json grain-origin-prepare REQUEST.json PACKAGE.bin OUTPUT_DIR
```

It exclusively creates `OUTPUT_DIR`, then retains `source.eml` and
`scope.json` with exact readback before success. The directory is set to
`0700` before any full-prefix bytes are written, and both files are set to
`0600`. Existing output paths are refused. The operator must control the
parent directory and other processes running under the same UID; POSIX modes
do not isolate those processes from each other. The request example reproduces
this fixture's article context and
selected signed targets; later R2 publications use the same command with
their own independently verified package and operator-selected request.
