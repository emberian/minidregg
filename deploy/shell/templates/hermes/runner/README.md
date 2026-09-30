# hermes/runner

Read by `summon ROOM as runner`, in this order: `budget.json` (step 2, the
account), `grants.json` (step 3, the delegations), `program.md` (step 4, the
program document Hermes reads on every attach). The steps are in `../README.md`.

The runner is the one role whose program cannot be filled in from the room
alone. `{INPUTS}`, `{OUTPUTS}` and `{TASK}` come from the summoner, and PLACE
§2.7's `summon ROOM as runner` has no argument that carries them. The proposal
here is `summon ROOM as runner --program FILE`, where FILE is this
`program.md` with those three lines filled in. `summon` parses the Inputs and
Outputs lines (comma-separated cell names) into the `inputs` and `outputs`
sets that `grants.json` delegates over. P-HERMES-ROOM decides this. A runner
with no outputs is not summoned.
