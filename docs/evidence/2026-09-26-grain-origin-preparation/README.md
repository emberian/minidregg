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

The first source-matched Mac native host
`/tmp/minidregg-overnight-20260926/minidregg-host-final-combined`
(SHA-256 `280654f522c382f7ebb6f801b90f960b519a3d3e622a3053ffc1a88e5c8f1566`)
ran that command under an operator `umask 077` and exited 0. Its retained
`source.eml` had SHA-256
`8b2da29b05723e1f4f48f1889f84a9e8037cbfef1a23ccc0c7ece04ae0f0a488`,
equal to the recorded R source; `scope.json` had SHA-256
`ce780f5ead654d56757313dd4362e1e2bf999767a98ac2ec4ef80ce53eed3b92`
and recorded the exact receipt image boundary, full package/prefix digests,
article headers and all signed target IDs. A second invocation with the same
output directory exited 1 with `already exists (error code: 17, file exists)`;
both retained hashes were unchanged. Its observed `0700` directory and `0600`
files follow the operator's umask, so this first image alone does not test
source-enforced permissions.

The permission-tail Mac native host
`/tmp/minidregg-overnight-20260926/minidregg-host-final-permissions`
(SHA-256 `22954f15df67cc19e46d42d70a89a67e4c980f1e051ffb08c64386b901bc9f6a`,
Main SHA-256 `4af37a4d95f8ed77865ea8b06385b35f0f099cc27d4b99bb4ad76658cb0be9e6`)
ran under **umask `022` with a `0755` parent**. It exited 0 and created the
output directory at `0700`, `source.eml` at `0600`, and `scope.json` at `0600`.
The source and scope SHA-256 values were exactly the same as the first native
run; scope retained the expected original image boundary and exact
package/prefix digests. Repeating the command against the existing output
directory exited 1 with `already exists (error code: 17, file exists)`;
source/scope hashes and modes remained unchanged. This tests local file
custody and exact preparation only; no fn signing, admission, or relay ran.
