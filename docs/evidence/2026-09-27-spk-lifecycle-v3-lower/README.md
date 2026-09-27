# Source-bound SPK launch lifecycle, lower source checkpoint

The 14 new Kernel modules listed in `source-sha256.txt` passed direct Lean
checks, one compiler process at a time, in the private hbox overlay
`/tank/dregg-build/minidregg-55d3868-launch-v2-narrow`. It used immutable
source/OLean prefix 292 (manifest SHA-256
`0c0b8fd0aedf4f97650d3ad4d369629e955943fd472c0ec089eb4de0f017d1cd`)
from the exact `55d3868` archive. Final direct compiler logs were empty. The
bounded method and per-module exit verdict are in `verdict.txt` (SHA-256
`54f0e44d289fe5849fa115bf9f2619da1030d9adcf33860093937f89543b05b7`).

The v3 BEGIN source derives `base.source.operationId` from a framed
authorization preimage containing the complete normalized base Source,
separate caller correlation ID, v2 launch descriptor, stable grain volume ID,
and START choice/binding. The existing native DRC signature checks that
source command; the special v3 `shape` refuses a caller-supplied mismatched
operation ID. `authorizationBytes_start_eq` proves that changing the chosen
action or prior-create selector changes the canonical authorization preimage.
It does not claim hash injectivity. `Accepted.signedInvocationBound` connects
the checked invocation to that source command.

The reusable package descriptor contains all ordered signed create commands
and the signed continue command. The grain binding selects one command digest
and a stable source volume ID; `volumeIdBytes` is exactly 32 cSHAKE output
bytes. Its physical custody record is signed and compared byte-for-byte;
Mini does not infer protected-volume ownership from a path, inode, empty
directory, or process PID.

The lower claim consumes a first-attempt nullifier when a create is claimed.
The lower completion can add a created marker only with a checked successful
running report, and it retains exact signed volume custody. A conditional
reader reconstructs the original successful completion, full intent and
receipt at its original prefix; its lineage law binds app, volume and custody
while allowing an independently authorized later package upgrade. These
lower candidates are **not permits**. The missing upper work is the
chronological `NativeHostReplay.Verified` join, special native receivers and
Host author/inspect routes for events 23–25. Old lifecycle replay remains
unchanged in this checkpoint. No resident process or linked native binary was
tested.
