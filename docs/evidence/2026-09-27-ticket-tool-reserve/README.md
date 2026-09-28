# Guarded event22 tool reserve

`scripts/spk-platform/reserve-ticket-tool.sh` prepares one ordinary
AgentGrain `reserve(3)` for the next event22 ticket. It pins the qualified
Mini and Host binaries, operator socket, private signer/config, signed current
tool7902 status 1 with reserved 0 and at least 3 remaining, and the exact
prepared `call.bin`. `send` fsyncs a one-send marker before Mini's existing
exact-call `retry --mode submit`. A lost reply permits only `lookup`; a second
send is refused. The readback checks tool status 3, reserved 3, unchanged
generation and remaining decreased by 3. Every readback retry gets a fresh
directory and query nonce, so an interrupted query cannot occupy the only
recovery path or reuse the previous query authorization.
Reserve nonces allocated to successive routes must be spaced by at least
10002: the helper may use `NONCE+1` for the before query and
`NONCE+2..NONCE+10001` for numbered post-reserve readback attempts.

`advance-ticket` is available only for the five ticket routes. It re-inspects
the exact retained event22 plan under the pinned Host, compares its source
decoded grain tool root and full before state to the reserved readback, and
uses read-only event22 lookup to match the retained four-field receipt. Only
then does it archive the active marker. Event27 is an ordinary birth and is
outside this tool-reserve path. No grant reserve or grant marker retirement is
implemented here.

The hbox schema fixture ran the exact script SHA in `SHA256SUMS`. It injected
a lost submit reply, refused a second submit, injected an interrupted
post-reserve readback and resumed in a numbered directory, rejected a changed
event22 plan, then matched the ticket receipt and closed the marker. It also
refused stale tool state and a world-writable Host binary without creating an
active marker. `schema-only-hbox.log` records the result; the two fixture
scripts are retained. This fixture uses a mock Mini and Host and makes no
claim about native Store acceptance. No r3 Store was touched.

Reproduction on hbox uses the retained fixture scripts at
`/home/hbox/mini-ticket-tool-{mock,test}-r8.sh` and the helper at
`/home/hbox/mini-reserve-ticket-tool.sh`; `test-restart.sh` fixes its own
fixture root to `/home/hbox/mini-ticket-tool-fixture-r8`. Use a new suffix
when rerunning, replacing `r8` consistently in both scripts so prior
evidence remains intact.
