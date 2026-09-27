# Agent lifetime reserve and grant custody client source

This source cut adds owner-private event 27 grant planning, detached-signature assembly, one-shot submit, and receipt-only lookup. It also adds grant-bound event 26 v3 reserve planning and sealing, with private op 80/81 authoring followed by the existing public exact-call op 2/3 submit and lookup. The v2 reserve path is unchanged.

The event 27 broker routes 72–75 are private. The reserve author route is `application-agent-lifetime-reserve-request`; its inspection type remains `application-agent-lifetime-author-request-v3`. The client checks ordered source-produced signing headers and pin/approval fields, retains exact ingress and attempt markers, and uses numbered read-only lookups after uncertain or lost submit replies. It does not send a second exact call from a marked attempt.

Validation on the shared source: `cargo fmt --manifest-path native/resource-client/Cargo.toml --check` passed; `cargo clippy --manifest-path native/resource-client/Cargo.toml --all-targets --locked -- -D warnings` passed; focused `cargo nextest run --manifest-path native/resource-client/Cargo.toml -E 'test(/agent_lifetime_grant::tests/)|test(/agent_reserve::lifetime_v3::tests/)'` passed 5/5. Logs are adjacent; the successful fmt check emitted zero bytes. Tests exercise client filesystem recovery and inspector field handling. They do not establish native event 27 acceptance or qualify provisional Host 80/81 routes. Native acceptance awaits a source-qualified Host route and an actual accepted event 22 ticket.

`SHA256SUMS` pins the four Rust source files and three retained logs. No live Store or broker was changed by this client gate.
