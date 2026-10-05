# M2: M1 + PayObservation no longer judges its clock write (the Prepared field, its
# construction and its theorem removed). Applied in a scratch clone, never committed.
import sys, re
root = sys.argv[1]
p = root + "/Kernel/PayObservationReceiver.lean"
s = open(p).read()
cuts = [
  ("""  /-- The clock's own committed law admits the advance (no fault). -/
  clockJudged : ReceivingLaw.judgeWrite (laws deployment profile) .payObservation durable
    (clock.write clockValid.apply)
    (some (clockStepOf deployment profile ambient command directory.directory authority.snapshot
      pay.cell clock.cell clock.clock plan clockValid)) = none
""", ""),
  ("""        match clockJudged : ReceivingLaw.judgeWrite (laws deployment profile) .payObservation durable
            (clock.write clockValid.apply)
            (some (clockStepOf deployment profile ambient command directory.directory snapshot
              pay.cell clock.cell clock.clock plan clockValid)) with
        | some fault => throw (.law fault)
        | none =>
""", ""),
  ("decided, clockValid, clockJudged,", "decided, clockValid,"),
  ("#assert_axioms Prepared.clock_lawful\n", ""),
]
for a, b in cuts:
    assert s.count(a) == 1, ("M2: anchor not found", a[:60])
    s = s.replace(a, b)
m = re.search(r"/-- \*\*The clock's own law admitted the advance\.\*\*.*?prepared\.clockJudged\n", s, re.S)
assert m, "M2: clock_lawful not found"
s = s[:m.start()] + s[m.end():]
open(p, "w").write(s)
print("M2 applied")
