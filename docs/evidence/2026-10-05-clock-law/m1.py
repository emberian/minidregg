# M1: the genesis clock law withholds the pay clauses (monotone + ticks only): a clock law
# that refuses a pay operation's advance. Applied in a scratch clone, never committed.
import sys
p = sys.argv[1] + "/Kernel/NativeHostGenesis.lean"
s = open(p).read()
a = "ClockLaw.clockPredicate (config.clockTickers.map (·.subject)) config.payObserver.isSome"
assert s.count(a) == 1, "M1: anchor not found"
s = s.replace(a, "ClockLaw.clockPredicate (config.clockTickers.map (·.subject)) false")
open(p, "w").write(s)
print("M1 applied")
