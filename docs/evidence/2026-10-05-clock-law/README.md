# Clock law judged by every clock writer: executed acceptance (2026-10-05, lane kn-law-bypass)

Three Host binaries built on persvati (`lake build minidregg-host`) from the lane commit (`hosts.sha256`):

* **L**: the lane as committed. The genesis clock law is `ClockLaw.clockPredicate tickers true`;
  PayObservation, PayEnrol and PayEnrolV2 judge their clock write with `ReceivingLaw.judgeWrite`.
* **M1** = L + `m1.py`: the genesis clock law withholds the pay clauses (monotone + ticks only), which
  is a clock law that refuses a pay operation's advance.
* **M2** = M1 + `m2.py`: PayObservation's clock judgement is removed (the Prepared field, its
  construction and its theorem). The law is the same as in M1; only the judgement is gone.

J-PAY-3 (`native/resource-client/journey.d/jpay3.sh`, its own Host and Store) on each:

| binary | row "P1 happy record ... at tip 1000" | row "clock is the tip" | verdict |
|---|---|---|---|
| L  | confirmed | clock=1000/1759250000 | PASS 24/24 (`jpay3-L.rows.tsv`) |
| M1 | refused `PayObservation.Reject.law (LawFault.lawDenied <clock cell id> {path := [0], clause := <the resolved clock law's failing disjunction>})` | clock=0/0 | FAIL (`jpay3-M1.rows.tsv`) |
| M2 | confirmed | clock=1000/1759250000 | PASS 24/24 (`jpay3-M2.rows.tsv`) |

So the refusal in M1 comes from the clock's own law, and it names the clause. M2 shows the turn
commits, and the clock advances, once the judgement is removed: the bypass that existed before this
lane. The named clause is the resolved law's top-level disjunction, because `LawLeaf.of` treats a failed
`any` as one clause. That is the DRC's own refusal naming, unchanged here.
