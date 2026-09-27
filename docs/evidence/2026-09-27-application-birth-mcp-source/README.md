# Application/session MCP catalog source gate

This source checkpoint exposes operator-allowed application and session birth
tools to the unforked Hermes MCP client. The controller constructs discovery
names from its exact retained Mini birth registry and checks the qualified
Host image before starting the broker. A session tool is listed from the
first `tools/list` when a session family is configured: Hermes may cache that
list, so its `application` argument is a bounded name string, not a dynamic
enum. The controller still rejects an unknown name before reserving and
requires the current signed app owner-cap read for a real session birth.

After a confirmed app birth, the same broker refreshes its bounded name hints
before returning the tool receipt. The 4 focused MCP tests include an
absent-to-confirmed name refresh on one broker; `cargo nextest run` passed
80/80 and strict all-target clippy passed. `cargo fmt --check` and
`git diff --check` passed after the comment-only final edit. Source SHA-256:

- `native/grain-runtime/src/main.rs`: `4beb6d0ee61f5e619100e5f36236b06baa7ffb9ccdf8d8c14d9e8b299c9e1847`
- `native/grain-runtime/src/mcp.rs`: `624bc65044623958a3f55751013413c43a3e552f01c6e702b187c44cf6b3c2e2`

The direct op30/31 native gate is separately recorded in
`docs/evidence/2026-09-27-application-current-birth/`. This catalog check is
source and local transport evidence only; the distinct hosted 9601 Hermes
fixture has not sent an app/session tool call at this checkpoint.
