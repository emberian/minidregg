# Private event22 plan preview

The resource client adds `mini grain-share-issue-plan --host HOST --config CONFIG.json --socket OPERATOR-SOCKET --request REQUEST.json --dir NEW-PRIVATE-DIR`. It authors and inspects the exact source Request, invokes only the private persistent Host op56, and retains the raw request, plan, frames, decoded views, config copy, and a plan-only hash pin in the new mode-0700 directory. It requires an owner-private request and operator socket. Its plan view must echo the full source-inspected Request and the exact canonical request/plan bytes. It does not read a signing key, approve slots, assemble ingress with op57, or submit event22. Existing `grain-share-issue-prepare` retains its separate approval/signing path and now uses the same request/plan view equality check.

Changed source pins:

- `native/resource-client/src/main.rs` SHA-256 `b65fb1240dc5df999b4a7e1c752a49b971ab353dad9a4fbded9711478eaa7c35`
- `native/resource-client/src/grain_share_issue.rs` SHA-256 `74210af50fe46e3a947093d3cab052c776570ac6ed219450ed1d0661fb4e25fc`

`cargo fmt --manifest-path native/resource-client/Cargo.toml --check` and `git diff --check` passed. The focused `plan_only_join_rejects_a_plan_for_a_different_request` test covers a swapped request presentation and changed Plan bytes. In the isolated cb55-derived Persvati source copy `/home/ember/build/minidregg-shareplan-mini-src`, only the two pinned files differ from the qualified base. `cargo nextest run --locked --offline -E 'test(/grain_share_issue::tests/)'` passed 5/5 (`nextest-r2.log`), and `cargo clippy --locked --offline --all-targets -- -D warnings` passed (`clippy-r2.log`). The first Clippy pass found an inherited warning on `decode_hex`'s `.chunks_exact(2)`; the final source uses `.chunks(2)` after the unchanged odd-length refusal, preserving two-byte pairs. No release Mini binary, r3 Store, Host service, key, or signing path was used for this source checkpoint. The CLI requires a new source-qualified release binary before an operator script invokes it.

## Subsequent committed release qualification

The exact `e1a36c0` committed crate was independently archived and built on
Persvati with two Cargo jobs and a4GiB limit. Release build passed in6.64s;
the archive's crate files matched the earlier tested source. The retained
[release manifest](release-e1a36c0.txt) pins the archive,33-file source manifest,
build log and binary. Hbox artifact
`/tank/dregg-build/minidregg-mini-e1a36c0/bin/mini` has SHA-256
`2c0fee88774e003c1eac9c9a715a0f9c18c5a92bbe862c1bc651d695ca757e6a`
and mode0500. It is ready to consume the existing persistent operator's op56;
the operator binary was not replaced. This build is not evidence of a live r3
ticket issuance.
