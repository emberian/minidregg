# Application/session birth runtime source checkpoint — 2026-09-27

This checkpoint is source-level. The runtime has operator-named application
(three resources) and session (two resources) family planning, complete
one-operation bundle journaling, exact current-author intent retention through
Mini op30/31, binary submit, and exact lookup recovery. Session selection
requires a reverified local application birth before consuming an ordinal or
reserving allowance; a fresh signed owner-capability read remains required at
execution. App/session calls require an operator-pinned Host executable SHA-256
and persistent socket. The MCP catalog still advertises content birth only.

The same source cut bounds metered provider sends using operator-pinned maximum
input/output tokens and the source-owned tariff before reserve. Live and
audited quote checks reject reported counts above those retained ceilings.
This is a provider/model accounting premise, not an invoice attestation or
external account spend cap. No paid provider request was made for this check.

Source SHA-256 (paths relative to the repository root):

| File | SHA-256 |
| --- | --- |
| `native/grain-runtime/src/main.rs` | `c0f758c2280fc779b10fade9adc414fc5b054766150175492caa1c8bc05b2a26` |
| `native/grain-runtime/src/application_tools.rs` | `6af688c5aefe98552cd8fe9e4a5e1bb8e197958bb68401dfb80fd70d329e7518` |
| `native/grain-runtime/src/resource_tools.rs` | `ff6b8cf92c6027479f6ac35b9a1947aaa679c1c6d4b06bc5fa970154f9477584` |
| `native/grain-runtime/src/publication_refusal_tests.rs` | `92cff7166847004c65018b60312b5806650547c6357b6e19f69839ea2ae58cef` |
| `native/grain-runtime/src/provider.rs` | `039c0e2b6677ac05a971b1267a2b24f72ae82c1b0cdde1b1d6a66fe4e4a811fe` |
| `native/grain-runtime/src/provider_profile.rs` | `0f76b323d601cf33bb67ec9c7b4ee62b6996ed51b5fce4e9ec8152a83ad49eb7` |
| `native/grain-runtime/README.md` | `c687e1b9b436c2ca3cb3bf33ba79e0579cd92026c8f589687c15462deb4326b2` |

Validation:

- Full `cargo nextest run --manifest-path native/grain-runtime/Cargo.toml`:
  79/79 PASS, run `59917cab-7172-4ea9-be9f-ac122add91e2`. This preceded the
  final session-selector ordering and Host pin changes.
- Focused `cargo nextest run --manifest-path native/grain-runtime/Cargo.toml
  -E 'test(/birth/) | test(/application_tools/) | test(/metered_/)'`:
  18/18 PASS, run `14adf79a-330c-4019-937b-94de6b474b1b`, after those
  changes.
- `cargo clippy --manifest-path native/grain-runtime/Cargo.toml --all-targets
  -- -D warnings`: PASS on the listed source hashes.

No linked op30/31 Host or native app/session admission verdict existed at this
checkpoint. No app/session MCP tool exposure or end-to-end Hermes action is
claimed. A source-matched native birth, restart lookup, and signed current
resource read remain required before enabling those tools.
