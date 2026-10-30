/-
# CensusChecks -- the census checks that no whole-tree census imports

`TokenCensus.SelfTest` plants a forgery per private constructor and must see each
refused; `TokenCensus.Fixtures` runs the token census over the recorded-run library.
Neither may be imported by `TokenCensus` (the first would put forgeries in the census
environment, the second a recording). The merge gate builds each by name.
-/
import TokenCensus.SelfTest
import TokenCensus.NativePinSelfTest
import TokenCensus.Fixtures
