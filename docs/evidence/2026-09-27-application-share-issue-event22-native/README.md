# Event 22 native share-issue acceptance

The first fresh hbox attempt (`run-r1`) stopped at a fixture assertion before
the event-22 reserve, plan, or op54 submit. Its metered app/session base passed.
The signed tool read returned generation 1, status 1, remaining 38, reserved 0;
the fixture expected status 3. `Kernel/AgentGrain.lean` defines status 1 as
running hard and status 3 as reserved hard. After settlement the tool correctly
returns to status 1. The same erroneous expectation appeared in the fixture's
post-issue assertion; both checks were corrected in a separate source cut.

The old attempt and Store remain intact at
`/tank/dregg-build/minidregg-event22-r5-client-session/run-r1` on hbox. No
event-22 submit or ticket was attempted in that run. The bounded user unit
`mini-event22-r5-client-session.service` terminated with exit 1 after 21:05.23
wall time. The copied view, base verdict, unit verdict, and timing are keyless
selected evidence; `SHA256SUMS` binds their exact bytes.

Execution used Host source `55d3868`, binary SHA-256
`a9e5cf96015b8439b596e602cd7685773dc5eebf96356bc0c8cc5f22b7c46f87`
(qualified manifest SHA-256
`b0e1ab49639e7b6ffc08f015d6bdffb0cbda67288a1325dd1e4f6f8a0032bf01`),
Mini source `007b513`, binary SHA-256
`a339b384f9a6c15d9c3f64e5df243b230da7e5a50d0b252cafbbcd94ad8e47ee`,
and source-matched `9746c47` Store/signature helpers SHA-256
`9a5054813d9ad358ece337b99121cb37a36ba82b4b92ad0e287dcc7e529190e0`
and `e80a0949d0ce16b24bcf24f2ac1306f4e194887ba11d328121b4c3345f8dfa1a`.
The executed fixture source SHA-256 was
`b88e3a05b7ec42e9b5d939f98ec44772d06a1e2c5317313ed5232132e3bcfdcc`;
the corrected source SHA-256 is
`b43298ae64854bb356a764b6b4de4c4776c14d7462d12a199e7f3507317e7e72`.
This is a failed assertion gate, not a positive event-22 acceptance result.

The fresh corrected `run-r2` passed that status assertion and the tool
reserve, then stopped before op54 during the wrong-header refusal check.
`r2-header-refusal.stderr` reports that the custody client could not find
`signing.canonical`. The retained native plan inspector decoded all 15
signing slots but emitted that field for none of them
(`r2-inspection-shape.json`; full private plan inspection SHA-256
`17fb161093789d8249ae746ac76460d85282f01e88a0a34f0636c587c3786979`).
The exact `007b513` client requires that canonical decoded header echo to
equal each source plan slot's header before it signs. The Host inspector now
re-encodes each decoded header, marks it decoded only on exact byte equality,
and emits `canonical`; production source SHA-256
`bb40ae6cb5640d8a3ad4712b8d762d9521e9554a79e3d920ac6ea69749bdccfb`.

The repaired single module passed Lean against the immutable cacc warm
closure in an independent Persvati path, producing private OLean SHA-256
`a4c2fb94f4ff50f5adcc1582ed02a4b2e6b963c1266f1bb195126162fc36de0b`
with empty diagnostics. Evaluating its inspector on the retained r2 plan
(SHA-256 `99c193363821795ccdf133be349593265eb43674a65d0062d9cb150202ef142f`)
gave 15 decoded slots and 15 exact `signing.canonical == slot.header`
matches (`r2-repaired-inspection-shape.json`). This is a source-evaluator
check, not yet a linked repaired-Host native acceptance. The r2 Store and
failed custody attempt remain intact at
`/tank/dregg-build/minidregg-event22-r2-client-session/run-r1`; no op54
issue or ticket was submitted.

The r2 fixture consumed 34:15.01 wall time, 1082.97 seconds user CPU and
192.60 seconds system CPU across its full process tree, with 562,228 KiB
peak RSS. Retained file timestamps bound the phase windows: the event22
pre-reserve signed read took 3:30.04 from intent to view; reserve intent to
confirmed outcome took 6:26.93 (its op2 call to outcome took 3:02.08);
tool reserved readback took 3:13.77; parent readback took 2:48.80; and
request bytes to preview plan took 1:21.56. These are artifact-to-artifact
wall intervals including process startup and replay, not isolated algorithm
timings. Per-phase CPU was not recorded; the total CPU above and observed
CPU-active native children do not justify finer attribution. `r2-total.time`
and selected keyless refusals, views, reserve outcome, and verdict bind the
terminal scope. A fresh repaired-Host run is still required for positive fee,
one-shot receipt, and reopen claims.
