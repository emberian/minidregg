# Event26 detached payer custody, source cut

The controller-only `mini agent-lifetime-paid-payer-sign` command reopens the sealed event27 grant and confirmed lifetime reserve, re-inspects the exact op78 plan, and requires the current op78 result to equal those retained bytes before using the protected payer key. Its approval requires the exact ordered target, observation, and authority payer slots (roles 4/8/1, index 0) under one custodian and explicitly refuses app/grant signer fields. It emits detached payer signatures only; resident app/grant signatures, op79 assembly, op76 submit, and fd3 delivery remain separate.

Exact changed source SHA-256:

| File | SHA-256 |
| --- | --- |
| `native/resource-client/src/agent_reserve.rs` | `d7fbb4e728661a010d52f025683e5e92acfac0d13c130fd5d2391707bf217132` |
| `native/resource-client/src/agent_reserve/lifetime_v3.rs` | `30f8216d7a449559d365722b73c77692fdd75081a2fe2b8dbadb9a80d755101d` |
| `native/resource-client/src/agent_reserve/lifetime_v3/paid.rs` | `e5798f4f8ff80ecf0dfbfcc0fcdbce7d966993b1e320a53a7fefe1d954dbc465` |
| `native/resource-client/src/main.rs` | `2478a8504e08570018f40419c6ff6a09a08a1f51669762a69cacb78b97d99c94` |

From `native/resource-client`, `cargo nextest run -p minidregg-resource-client -E 'test(agent_reserve::lifetime_v3::paid::tests::)'` passed 5/5 paid-custody tests; `cargo clippy --all-targets -- -D warnings` passed. Exact bounded logs are `nextest.log` and `clippy.log`. The focused tests cover the three-slot shape and mixed-custodian refusal, retained receipt, assembly framing, and no-resubmit lookup behavior; they do not establish a native detached-signature journey. No Mini Store, paid provider, or SPK fd3 dispatch was used for this source cut.
