# SPK platform base r1 preflight refusal

The independent hbox run `mini-spk-platform-runbase-r1-client-session.service`
(invocation `3f37cb04cfe34833b7ffdd179072ce5b`) used the signed GitWeb SPK,
qualified v2 Host `4fba53294067013e3f32c012733375bcf51a8ef7895e996d2bdd605bc3c75506`,
qualified `spk-host` `2819d365dbc50a9becde45e991bf6f035e823073b12d97228407d9a412f30b01`,
exact Mini `007b513`, and committed `f8bc6bf` run-base source
`c5a43b1984cfe36458c44cc189670b8be3d60bb3f0fce2d9d7e5812e0ed3c6d0`.
Its offline signed-SPK v2 qualification completed. The positive-fee base then
exited 2 in 45.81 seconds **before creating a Store**. The failed private root
`/var/lib/minidregg/spk/fixtures/gitweb-v2-20260927-client-session-r1` remains
unchanged for audit.

The preflight generated three lines matching the old broad
`initialBalance.*1000000` guard: two quoted base balances rewritten from 100,
and one preexisting unquoted agent balance from the source overlay. The guard
expected two. `r1-boundary.txt` records both source and generated counts and
the absent `base` directory. No app, lifecycle, or installed-SPK result exists
from this run.

The source correction counts the two exact quoted rewritten fields in
`native-positive-base.sh` and checks the agent line independently in
`run-base.sh`. `sh -n`, ShellCheck, `git diff --check`, and the retained r1
overlay compatibility assertions passed. Fresh r2 must use a new private root;
this is a source/preflight correction, not native acceptance.

Fresh r2 used committed `6dacab3` scripts and passed the corrected overlay
preflight and offline v2 qualifier. It reached fresh workroom birth, then the
Mini Host rejected `$.birth.genesis.expectedSemantics` as different from its
source-derived profile; the run exited 1 after 52.07 seconds. Its Store and
attempts remain private at
`/var/lib/minidregg/spk/fixtures/gitweb-v2-20260927-client-session-r2`.
`r2-profile-shape.json` shows the authored birth and operator profile carried
the same expected semantics and grain tariff, while the operator config has a
completion custodian key. `Host.Json.birth` reconstructs a temporary native
profile without that configured key, which is part of runtime parameters.
The source repair must preserve the exact semantics equality guard; this r2
result is a real refusal, not an installed app or session.
