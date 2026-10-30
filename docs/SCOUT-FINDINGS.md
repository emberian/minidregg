# Scout findings

Present state, rewritten whole. Candidate under test: `c7aa7e8c4` (binaries identical in behaviour to
`41590f420`, which passed the tour 73/73). Run: every row of `scripts/pipeline/journey-rows` through the
tree's own `journey-runner` on hbox, keep-going, two rows at a time; evidence under
`hbox:/ci/scout/r1/c7aa7e8c413de0231f4734d2acc27efc5dea3c20/rows/<row>/`.

## Faults

| fault | repro | evidence | suspected owner | status |
|---|---|---|---|---|
| JPAY6 40/42: the consent plant authored the provider purse with the plain `birth-intent` kind (an ordinary birth, which the thin arm owns and frame 230 refuses by name), so the pinned purse was refused and the discriminator had no grain side. Red on every candidate back to 2b8f75dc (10-29 01:50); the product behaves correctly (checked by hand with the candidate's own host and consent binaries: plain pinned 255 thin, plain rogue 255 provider-route, grain pinned 230, grain rogue 255 provider-route) | `journey-runner --row jpay` | `hbox:/ci/scout/bis/<sha8>/r/*/rows/jpay/JPAY6.err`; fix verification `hbox:/ci/scout/r719` | driver (jpay6.sh) | FIXED on `lane/scout` `7d29a02d6` (purse authored as `grain-birth-intent`, ordinary plant stays `birth-intent`); verified on 719d7b7aa: JPAY6 42/42, jpay PASS=6 |
| K-CLOCK (KC) 22/33 in the demo set: starts at head 8 with nothing certified, then 200 ticks plus the 30-birth race spend the L = 256 tail before any certify ("head 257 certified 0 bound 256"); every later row is a shadow. KC is in no gate | `JOURNEY_STEPS="J0 ... J8 KC" journey.sh` | `rows/demo` (step logs copied to `hbox:/ci/scout/ev/demo/KC`) | harness (integrator) | FIXED on `lane/scout` `4704d2e33` (`jclock.sh` certifies inline before both phases); verified alone, K-CLOCK PASS 33/33 |
| fleetsign: 1 of 100 interleaved turns failed (charlie turn 28 transfer): `mini: cannot read .../attempts/a-2202.../plan.frame: No such file or directory` while the live attempt is `a-2686...` | `journey-runner --row fleetsign` | `rows/fleetsign/evidence/interleaved/charlie-28.json.stderr`, `interleaved.tsv` | integrator (client attempt-dir handling under concurrent profiles) | load-triggered flake: 4 of 4 reruns alone PASS (13-37 s); the one failure came with the box at load 8-9 and 3 other rows running. Attempt-dir race not yet pinned |
| JWF (web) 1/72: parity row. The shell verb `apps` (`apps list j`) has no visual web face | `journey.d/jweb-frontend.sh` (demo set step JWF) | `hbox:/ci/scout/ev/demo/JWF/hook.out` | app-reds lane / web | open, sent |
| demo row (the J0-J8 spine plus 51 steps) cannot finish inside its wall budget on a shared box: 29/46 steps; KTPL 707 s, J17 862 s, JDV hit its 660 s hook limit, then 12 steps never ran ("journey wall budget spent": JPD JCHAT JFEEDBACK JPAYE1 JPAYE2 JPAYE3 JP2 JDISCLOSE JESC JFLEETIN JSLK JSGM JR17). Those twelve are UNRUN, not green | demo row at `PIPELINE_ROW_TIMEOUT_S` default 5400 | `rows/demo/journey.err` | harness (integrator) | rerunning on 06831831 with a 12000 s row timeout |
| (shadow-set artifact, not a product red) J14 step: `install-controller: path must exist without symlinks: .../bin/grain-runtime` and sshe2e `manifest .host does not name its candidate output` | only on my symlinked shadow set | `rows/demo/journey.err` | none | not a fault; gone on clean-manifest sets |
| candidate `manifest.json` points at the `<sha>.tmp` build directory, so any consumer of a published set (journey-runner, `sshe2e` via `run.sh`) fails with "manifest .host is not executable" / "does not name its candidate output"; the gate avoids it by writing its own manifest | `journey-runner --tip <sha>` on `candidates/` | `rows/journey/row.err` on the first attempt | integrator (publish step) | open; worked around with a shadow set |
| exchange: `wrong-root unexpectedly installed` | `journey-runner --row exchange` | `rows/exchange/exchange.err` | fn (out of the demo) | open, low priority |
| KTPL took 707 s for 196 rows inside the demo row (law 17 watch) | demo row | `rows/demo/journey.err` | measure before judging | open |

## UNCONFIGURED rows (not red)

objective (no lean env for the tip), hostupgrade (no previous candidate set), m7 (no `M7_REFERENCE`),
m6grain (needs the sudoers rule for the run's source), hermes (unit `mini-grain-controller@8751`
already loaded on hbox: another tenant's, a port collision), births and perf (workload passed, the bar
was not judged because the box was not quiet).

## Passing rows

journey, rooms, activity, seats, bounty, call, send, domain, upgrade, objectrecord, welcomecontinuity,
m3, m4, m8, jbend, chargedfailure, jserve, jprivate, rate, births (N=64: p50 382 ms, p99 1072 ms),
perf.

## Off-script stress (candidate 06831831, one J0-J4 world, `scripts/scout/stress.sh`)

| probe | result | verdict |
|---|---|---|
| 8 concurrent writers, same field, same expected value | exactly 1 wins; 7 refused `stale-target` ("target moved since the plan was signed") | PASS, no lost update |
| 200 000-digit scalar value | refused by the client: "scalar value must be a canonical signed decimal"; Host answers on | PASS |
| 5000-action request | refused client-side: request must be 1..=262144 bytes | PASS |
| malformed JSON request | refused by name (EOF while parsing) | PASS |
| 200 silent connections on the Host socket, then an honest read | read answered (value unchanged) | PASS |
| `kill -9` of the Host mid-write, restart | client reports "uncertain host response: connection closed"; after restart the write is present exactly once (102 to 1102); a reused attempt directory is refused ("unused direct child") | PASS (retry must go through the lookup path; my script reused the directory) |
| aging: 200 sequential write+read, certify every 100 | write p50 233 / 216 / 199 / 271 ms per block of 50 (max 415); read mean 114 ms (first 50) to 141 ms (last 50) | watch (law 17): mild growth in the last block, inside noise at this size; a 1000-record run is the nightly growth row |
| jcertify on 4e5faa8d (infra's fixed script) | PASS: 320 records, zero tail-bound refusals, certify confirmed under 120 concurrent writes, racedRefusals=0 | PASS |

Not yet probed: aged worlds beyond 200 records (AGE), many page loads (the ~206-GET budget), Hermes under load,
store restart under load (the single in-flight kill above is the only restart probe).
