# Event22 future-run fixture: one session for routine reads

`scripts/application-share-issue/native-grain-acceptance.sh` SHA-256
`c59dd81b830c7af40df2f1752cff3ed2ddb42de2b13f21a8cfd1ef7bee4be34f`
now starts its existing public `mini serve` session before the first
pre-reserve read. The three pre-issue signed reads and the reserve submit use
that socket; payer-balance and two post-issue reads use the existing operator
socket. Each `mini query` still obtains a source Host challenge and submits a
signed observation. The service's `NativeHostSession.refresh` rereads complete
current Store bytes on each operation, reuses a verified tip only on exact byte
equality, and checks changed history before query admission.

The public op56 refusal remains on the first public socket. The script then
stops that service and starts its distinct owner-private operator service.
After issue it stops and starts a new public service for the ticket read, then
stops and starts a new operator service for receipt-only lookup. These are the
existing explicit cold-reopen acceptance gates; no additional cold read is
needed. The PID trap and socket ownership remain unchanged, and each run still
requires a new evidence directory. The prior r3 attempt and its archived script
and Store were not touched.

This is a script-only source check, not a native acceptance result. `sh -n` and
`shellcheck -s sh` passed. Source review confirmed public op4/op5 and op2 are
allowed, while op56 remains operator-only; the script still expects its public
refusal. No Host process, Store mutation, or acceptance fixture was run.

The retained r2 pre-reserve query interval of 3:30.04 covered a direct
`mini query` with no socket, so it launched separate cold challenge and query
Host processes. The separate f461 query benchmark measured a fresh direct CLI
Host process at 81.72/83.04 seconds; it did not measure a warm stdio query.
The earlier same-image session evidence measured approximately 1.5–1.7 seconds
per warm read/lookup. The future fixture must report its own startup, first
query, later query, submit, restart, and receipt timings before claiming an
end-to-end improvement.
