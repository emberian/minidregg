# Resident BEGIN-v2 operator routes (source check)

This cut adds private native Host op50 (current-image INSTALL/START BEGIN-v2 signing plan) and op51 (detached signature assembly). The operator config fixes the app, package and snapshot resources, management subject/key, and capabilities. Op50 obtains a verifier-current session. Op51 returns canonical ingress; fresh op22 performs the actual native admission and current-image check. The resource-client broker admits 50/51 only on its owner-private socket.

Frozen source SHA256:

| Module | SHA256 |
| --- | --- |
| `Host/ApplicationLifecycleBeginOperator.lean` | `057be08bb9dd93f9a7fbc0ed1254cd6d9a03a3195ec2fef037fc2ebc7f3113b6` |
| `Host/Json.lean` | `45ac646ea454706f2ccf3481ce34c8c16c8476a5a3fb096a0a8a696d7808b122` |
| `Host/Main.lean` | `51b9bbe4a13f4a631e0561deaf2d01bff1c0eb2a73c414f7bfdccd45ddec2a1a` |
| `native/resource-client/src/transport.rs` | `d7a5bb72df88db2a1e95324bc995a6400419e52981d0271aa17c66405a904132` |

The three Lean modules compiled serially with direct `lean -R ... -o ...` on Persvati in private writable `/tmp/minidregg-begin50-main-check`, using source-matched fn namespace Main and completion overlays over the selected-prefix base. The final Operator and Main logs are empty; Json emitted only existing axiom and linter warnings. Final OLean hashes: Operator `d62e833f10dc5bcfe1937e7eb5a8592be9cc156da2609d5e4a2ccc532c7292b7`, Json `6318cc1e7ad0882f02567137ad9a03bd6f8ca99198f23951b52965346220de6c`, Main `0a3857f227a02b633d44698a0d4eef6d6315c5d9934989bea094b4948bb7a60c`.

The focused `namespace_and_lifecycle_authoring_routes_stay_private_and_bounded` nextest test passed 1/1 using isolated `CARGO_TARGET_DIR=/tmp/minidregg-fn-operator-transport-target`; `cargo fmt --check` passed. This is a source-only gate. It does not claim a linked Host binary, signed BEGIN, or physical admission.
