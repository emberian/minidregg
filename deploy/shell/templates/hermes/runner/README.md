# hermes/runner

Read by `summon ROOM as runner --program @FILE` (compiled into `mini`).
`{INPUTS}`, `{OUTPUTS}` and `{TASK}` come from the summoner: FILE is
`program.md` with those lines filled in (comma-separated cell names this
founder holds). `summon` delegates observe+mutate on each output and observe
on each input; it does not change their laws (the outputs' laws are the
founder's: a law that does not admit Hermes refuses its writes, which is the
point of a law). A runner with no outputs is not summoned. The worker is the
same controller as the librarian's (`grain-runtime hermes-room`).
