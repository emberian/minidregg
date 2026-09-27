# Registered shared application references: source checkpoint

Commit `db3b187` adds operator-configured foreign application names to the
grain runtime's tool catalog and session selector. A reference is a discovery
pointer, not a locally born resource or an owner capability. Before a selected
session birth, the controller rechecks the exact historical application birth
receipt, the source-specific share-issue receipt, and four current signed
resource reads using this tool subject's separate observe grants. These native
operations run under `CustodyGate`; hard disconnect cancels and reaps their
children. The selected evidence remains distinct in durable `BirthPending`.
Lean's current session-birth author and later dispatch admission remain the
semantic authorities. The four reads are separate observations and do not
claim one image-level join.

The original share issue attempt retains its private operator socket pin.
Historical op29 lookup uses the current controller's fixed public Host socket
override, which the native client supports; the retained ingress, Host, config,
and original receipt are still checked. A focused test uses deliberately
different original and current socket paths. Framed terminal status reports
only `registeredSharedApplicationCount`, plus existing safe state flags. It
never renders names, capabilities, paths, or the private journal. Pending
dispatch work now prevents a false `ready` status.

Source SHA-256 at this checkpoint:

| File | SHA-256 |
| --- | --- |
| `native/grain-runtime/src/main.rs` | `f1a62294891c8f65714b2b5aa9dec465d5e9be4ce749f5a0d2b191367e9da34d` |
| `native/grain-runtime/src/shared_app_refs.rs` | `a4f65adf0cbfb00902f808440003e2a1420f36fabb19895021e25910860e79df` |
| `native/grain-runtime/src/resource_tools.rs` | `be5543c7bc61b40addc56be3fffc703872b338d87cc3b0ba4e0ca02c85e5dcf5` |
| `native/grain-runtime/src/terminal.rs` | `2a9599586ca044dff717494a04acb81e63178a3f9f447460edcaabc91f9db132` |
| `native/grain-runtime/src/application_tools.rs` | `2da4d946626c6de905a54c83890b62d72b8452fa6050d9221b2aa9b702e3a5d8` |
| `native/grain-runtime/Cargo.toml` | `e41597a7ba20db75a1a0a417f5a19b36fb97d1ddb72943c57a2427afc922dcce` |
| `native/grain-runtime/Cargo.lock` | `00e706c9a4aeecb98dcf76ecab7f2794135c9ce3e2eddc4ea8e737956ce7e24e` |

Validation used a private copy of this exact source at
`/tmp/mini-shared-app-integration-check`, with an isolated Cargo target:

- [Focused nextest log](nextest.log): 22/22 passed, including tampered pins,
  distinct socket routing, supervised read refusal, and terminal projection.
  SHA-256 `d88b3de481dfb3bab5fd1e93dada56b54f09921ff60c421be82d69e2516935d5`.
- [Strict binary Clippy log](clippy.log): passed with `-D warnings`.
  SHA-256 `a9f056c98f8578445c71ed0ec681a264adf4ef54e855649e2913593f80ebd425`.
- `cargo fmt --check` passed; the captured [format log](fmt.log) is empty.

This is a source and focused-test checkpoint. It has **not** exercised two
independently authorized controllers against one installed application Store,
nor proved that a shared reference alone permits session birth or API dispatch.
That native acceptance requires a second controller's own current grants and
source-admitted session/dispatch receipts. No private keys, full journal, or
signed resource page is included here.
