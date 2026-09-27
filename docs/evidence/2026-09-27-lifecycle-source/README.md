# Lifecycle BEGIN source check

September 27, 2026. The four lifecycle files committed in `de48441` passed a
serial narrow Lean check against the current committed permission schema and
v2 application manifest. The six exact source hashes are retained in
`source-sha256.txt`; `verdict.log` records each module's start and PASS.

This ran in an independent Persvati copy at
`/home/ember/build/minidregg-overnight-20260927-lifecycle-narrow`, based on the
previously qualified warm application-authoring copy. One Lean process ran at
a time with two threads, under a systemd unit bounded to 64 GiB and 200% CPU.
The source manifest SHA-256 is
`06a45408f8155181ea697960809869071128bc2c0395e8eec0accf19a5322474`;
the verdict log SHA-256 is
`aa5db304664e985ba6671c148c38dadff1fb9e830448ab806bdb8d0bfc225c32`.

This verifies source elaboration and the named lifecycle checks, including
canonical source identity, same-image package observation guards, retained
DRC writes and special event identity. It does not establish a linked native
Host route, a Store acceptance run, a current physical claim, or an app launch.
The earlier local check used an older manifest dependency; this record is the
subsequent current-schema/current-manifest check, not a relabeling of that run.
