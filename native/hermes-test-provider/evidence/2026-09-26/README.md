# Real upstream Hermes to Mini publication, r5

This bounded evidence is from unmodified upstream Hermes ACP using the local,
deterministic OpenAI-compatible protocol fixture. No paid provider was called.
The fixture chose tool calls; Mini's signed read, joint observation, and native
settlement remained authoritative.

The Linux run used parent grain 7101, tool grain 7102, and publication object
7003. Hermes first called `mini_read_resource` for the allowlisted publication.
The fixture extracted its signed `view.page.root`, then Hermes called
`mini_publish` with that root as `expectedTargetRoot`. The native attempt's
`tool-settle-outcome.json` confirms installation with `acceptedCount: 10`.
An independent signed resource query changed the object root from
`33123752497037221731231169017086294867303331174554263998024751327768383133892`
to
`55070908931993074135985362517665169451634431671625479692889086081017559966815`
and shows object 7003 field 0 with value 1.

The controller and its sandboxed MCP proxy were byte-identical Linux binaries
with SHA-256
`708f26175249b18a5cd4a4b1cc33065295ead6221ca7eb6bd729524cd0846cd7`,
built from the frozen joint-grant fix (`main.rs` SHA-256
`b4a2449ff1b6469e5c453af6508c66f3a7095d89f90bda3f8108beb3e6230e1a`).
The fixture source for this run was `src/main.rs` SHA-256
`c7d0e85892b32b4d13c8ce0401f0d74be464df11c32a0cda9c6f0f1cca8e88c5`;
its Linux binary SHA-256 was
`e9aa692233cb44fff1c3200ddc31b3fbc6c2eba564a4481ce81f96a1ec3375cf`.
The fixture has subsequently gained a second-prompt behavior, so this source
hash distinguishes the run from current source.

`tool-settle-call.bin` is the exact accepted native call, SHA-256
`08039ed4dbc44ab786e520a3326c59fc16c7ade55b4dd56fc231aff6dbf86f99`.
`tool-settle-source.json` records the three ordered observation grants.
`provider.log` contains only bounded stage metadata and no prompt/tool bodies.
`result.json` is a curated projection of the original raw result at
`/tmp/mini-hermes-provider-codec/evidence-real-r5/result.json` on Persvati,
SHA-256 `c7677db935f2cc12dd9d3073e167171075f7c489fa8b287230f0ed1948bd01ac`;
it excludes the runtime binding and config paths. The journal projection retained
Hermes session `61a3176e-4a07-4a4f-9a3a-11b678a95e3e` but recorded the old
workspace fingerprint issue; **r5 proves initial `session/new`, not
`session/load` continuity**. The earlier r4 attempt was refused at the joint
observation footprint and is excluded from this acceptance evidence.
