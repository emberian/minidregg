# Birth authoring uses the deployed runtime profile

The integrated GitWeb base r2 stopped during birth authoring because JSON
reconstructed a runtime profile without the configured completion custodian.
The expected semantics in its genesis, operator profile and deployed Settings
agreed; weakening that comparison would have hidden the actual defect.

`Host.BirthRuntimeProfile.select` checks supplied deployment, federation,
template, creation tariff, genesis height and grain-birth tariff against the
deployed configuration, then returns its complete profile. The general
`select_without_custodian` theorem proves that dropping the optional custodian
from the supplied subset still selects the complete configured profile.
The unconfigured author retains its historical standalone behavior.

Both direct Host authoring and stdio op7 pass the deployed configuration.
Application/session authoring against an opened image also passes it, while
retaining the existing current-height, seed and current-authority checks.
JSON's expected-semantics check remains mandatory. An omitted grain-birth
tariff inherits the deployed setting; a supplied conflicting tariff refuses.

Serial direct Lean compilation passed for the helper, Json, current birth
authoring, Main and executable check module. The executable check passed the
existing eleven application-birth cases plus ten configured birth routes,
ten wrong-custodian refusals, seven configuration mismatches and a loaded
context check preserving current height and complete semantics. These are
source execution checks, not evidence that the integrated native run passed.

The independent Persvati workspace was
`/home/ember/build/minidregg-birth-profile-root-20260927`, using Lean4.30.0
with two threads and serial compiler invocations. Its writable OLean tree
copied the qualified f461f39 baseline and the source-matched event26 closure;
it did not modify either baseline. Earlier attempts failed because modules
were missing from the private overlay, before the final successful checks.
Logs and the tested source bytes are pinned by the repository-root-relative
`SHA256SUMS`. A new source-qualified native Host remains necessary before
retrying the failed integrated base with this fix.
