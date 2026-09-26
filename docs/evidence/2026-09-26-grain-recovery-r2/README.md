# Lost MCP reply and soft ACP interruption: partial native run

This fresh persvati fixture confirmed one native object 7003 publication after deliberately dropping its MCP reply. The runtime durably indexed the confirmed call as `publicationReceipts[0]` for ACP session `recovery-fixture`, with `reported:false`. The deterministic ACP protocol peer then exited without a first prompt response, as planned. It wrote a placeholder private `state.db` for the runtime fingerprint; it was **not upstream Hermes or an actual Hermes SQLite transcript**.

The intended next-prompt report did **not** run. The first attachment was soft. On the abnormal ACP exit, runtime submitted parent `cancel` from generation 1/status 4/reserved 3 to generation 2/status 7. Audited parent settlement of charge 1 moved status 7→6, leaving remaining 99/reserved 0. `reconcile effects` succeeded. The attempted second soft attach from generation 2/status 6 was refused at native admission. Status 6 is intentionally terminal for an explicit cancellation, so this exposes a missing abnormal-interruption transition; it is not evidence that a historical receipt was delivered. The controller unit was stopped and released with no worker running.

The selected public evidence is `publication-outcome.json`, signed `before-publication-view.json` and `after-publication-view.json` (different resource roots), `selected-journal.json`, `transition-sources.jsonl` (operations 26 cancel, 30 settle, 35 refused attach), `refused-reattach.json`, and `artifact-digests.sha256`. Full private run evidence remains `/tmp/mga-recovery-native-r2-20260926` on persvati. No custody keys, Store, binary calls, or private runtime config are copied here.

## Exact run image

| Component | SHA-256 |
| --- | --- |
| Certified Linux Mini host-next | `41647562c7dd1fe6cdf41836aa62c61fd7b24314f883b2bb14cb38779707c49a` |
| Linux grain runtime ELF | `8126b3432c56b040219ef53436a740f123813ee3658888663aa0f0e3df78ff30` |
| Runtime `main.rs` / `mcp.rs` | `28bb49e187964f1606433f6d51cec5154b4fe9e07cb68194d2981b16a73eaa27` / `03b4963831f44a77b9b4051dac98f86ef1dbe30a1cf2662d565b5bcc23a08ef4` |
| Focused runner | `92e3e56e430eda6dd5094403c7cf8d6a793bacff85868563c53ca8da62aac01e` |
| Restart-safe Mini helper | `b0884d2bee8f2cf38e7f7fa8cd17ded48b85fd0bf9bb440fcc9b44250a36661f` |
| SQLite Store / signature helpers | `ad03aede839259c1884383fc97f141a3fe106ba2f2cbae0df6f7916676fe193f` / `c84004123ae6f02654cb6749e4105e351199618aaefce5755a2a0bb10bd0892b` |

The runner's immutable private source manifest is `/tmp/mga-recovery-source-r2-20260926/manifest.sha256` on persvati. The earlier `/tmp/mga-recovery-native-20260926` fixture failed before any ACP child or publication because it mounted the protocol peer under the wrong executable basename; its controller also stopped. Neither run is a full receipt-recovery PASS.
