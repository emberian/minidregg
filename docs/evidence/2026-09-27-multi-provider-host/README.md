# Multi-provider Host and Rust source checkpoint

The Rust consumer cut selects one operator-configured provider metering entry for
the configured provider task. It keeps the existing single-provider quote metadata
wire as v1 and emits v2 metadata with an explicit resource ID only for the new
`providerMeterings` list. The metadata version is retained in the provider attempt;
old journals deserialize as v1. Retained report validation reconstructs the exact
selected metadata before settlement. The resource client checks that a v2 quote
names the same selected provider ID.

Source files (SHA-256 at this checkpoint):

- `native/grain-runtime/src/main.rs`: `40a24ea5f2eb703985da5cd966db3121787d9862a605520fbc83043cce4b593c`
- `native/resource-client/src/meter.rs`: `52909d141425f777234abae7abc78267d307c617e3285c408b143c5bccb85c1a`

Lean Host source files (SHA-256):

- `Host/Main.lean`: `36cccb3bd6bccc88b4d0c218e590063b8dcb49e7ad436d102582a68c8f6a346d`
- `Host/ProviderUsage.lean`: `ca41d991dcae2e3350b3ea705144bcdae1279308e9c7b59a183578c303621854`
- `scripts/provider-services/Check.lean`: `2f92be80ec06b9e55a07b1b41c738d4531ea399ba74fcdbf00e073759569db83`

The Host adds a bounded, unique `providerServices` list while retaining the
single-provider settings. Op17 keeps its v1 frame: it selects exactly one
configured provider resource from the source-decoded signed call targets,
then applies the original exact receipt, admitted-record, physical write and
suffix continuity checks. Op19 keeps strict v1 metadata for the scalar pin
and requires strict v2 metadata with `providerResourceId` for the list. The
multi-provider profile emits `providerMeterings` with the existing tariff
fields and no scalar `providerMetering`. A separate bounded
`agentLifetimeDispatchServices` list allows multiple event26 plans, including
distinct apps funded by the same purse; all four authoring operations require
exactly one complete `matchesFixed` selector.

Lean qualification used immutable baseline
`/home/ember/build/minidregg-8c13c42-native-20260927` and private writable
overlay `/home/ember/build/minidregg-multiprovider-check`. Direct Lean 4.30
compilation of `Host.ProviderUsage` and then `Host.Main` exited 0 with empty
diagnostics. Source-matched OLean SHA-256: ProviderUsage
`de7733fad1299917674bb0d13e10cf3aff921c3c5cdf706591d590243648dd57`,
Main `d082abf0741f14e577a56ac814be4aef1b3deedca23ac55cd234d9a032550c7f`.
The focused Lean check in `LEAN-CHECK.log` passes duplicate/zero service IDs,
wrong and ambiguous signed call targets, actual scalar-v1 and list-v2 HTTP
quotes, unknown provider and wrong model, same-purse distinct full event26
pins, duplicate pins and mixed full-selector refusal. The scalar/list mutual
exclusion checks were source-reviewed in `loadSettings` but not exercised by
that focused check.

`SHA256SUMS` records all source files and the bounded Lean check log relative
to the repository root.

Checks from each crate directory:

- `cargo nextest run --bin grain-runtime`: 136/136 PASS, run ID `0e707dbc-d511-4f85-ae03-47d6ff9cc634`.
- `cargo nextest run` in `native/resource-client`: 101/101 PASS, run ID `090d23a8-7f0e-4870-bd01-8528d6b55447`.
- `cargo clippy --all-targets -- -D warnings`: PASS in both crates.
- `cargo fmt --check` and `git diff --check` on the owned source: PASS.

These are source and component checks. No source-qualified combined Host/Rust
native call or same-Store A/B provider journey is claimed here. The r3 Store
remains under the app recovery owner's exclusive control.
