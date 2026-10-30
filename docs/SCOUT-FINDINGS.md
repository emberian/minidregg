# Scout findings

Present state, rewritten whole. Candidate under test: `c7aa7e8c4` (binaries identical in behaviour to
`41590f420`, which passed the tour 73/73). Run: every row of `scripts/pipeline/journey-rows` through the
tree's own `journey-runner` on hbox, keep-going, two rows at a time; evidence under
`hbox:/ci/scout/r1/c7aa7e8c413de0231f4734d2acc27efc5dea3c20/rows/<row>/`.

## Faults

| fault | repro | evidence | suspected owner | status |
|---|---|---|---|---|
| JPAY6 40/42: the grain purse's birth intent on frame 230 gets the thin-birth refusal (op 255, "a thin birth is consented with the member's source (thin birth frames 234/235)") for both the pinned and the rogue tariff; the plant rows (`consent refuses a purse law off the pinned tariff`, `discriminator (plant)`) fail. This is the regression `98064edba` fixed, back again | `journey-runner --row jpay` (or `journey.d/jpay6.sh`) | `rows/jpay/JPAY6.err`, `JPAY6-detail.err` | integrator (core: `NativeThinBirth.thinBirthIntent` discriminator, birth-source change) | open, sent |
| K-CLOCK (KC) 22/33 in the demo set: starts at head 8 with nothing certified, then 200 ticks plus the 30-birth race spend the L = 256 tail before any certify ("head 257 certified 0 bound 256"); every later row is a shadow. KC is in no gate | `JOURNEY_STEPS="J0 ... J8 KC" journey.sh` | `rows/demo` (step logs copied to `hbox:/ci/scout/ev/demo/KC`) | harness (integrator) | FIXED on `lane/scout` `4704d2e33` (`jclock.sh` certifies inline before both phases); verified alone, K-CLOCK PASS 33/33 |
| fleetsign: 1 of 100 interleaved turns failed (charlie turn 28 transfer): `mini: cannot read .../attempts/a-2202.../plan.frame: No such file or directory` while the live attempt is `a-2686...` | `journey-runner --row fleetsign` | `rows/fleetsign/evidence/interleaved/charlie-28.json.stderr`, `interleaved.tsv` | integrator (client attempt-dir handling under concurrent profiles) | open; reproduction runs in progress (see below) |
| JWF (web) 1/72: parity row. The shell verb `apps` (`apps list j`) has no visual web face | `journey.d/jweb-frontend.sh` (demo set step JWF) | `hbox:/ci/scout/ev/demo/JWF/hook.out` | app-reds lane / web | open, sent |
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
