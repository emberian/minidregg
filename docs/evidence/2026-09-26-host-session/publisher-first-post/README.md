# First durable origin publisher POST

One public `mini origin-publish` invocation ran against a fresh A Mini catalog
and a fresh qualified fn A Store. The client binary was built from commit
`dee5f8d` (SHA-256
`4e4beea360b5c0144b49ac6e4a08132e1ab7646d08a8a532bcc9091ba9c0b982`);
the native Host was `/tmp/minidregg-overnight-20260926/minidregg-host-postbbf`
(SHA-256 `919c3b7b64b7bff11d47a52993c7700b8028aa8596013cf396f41fd4f98c3038`).
The private state is retained at
`/tmp/mini-fn-publisher-r5-20260926/publish-state` (mode `0700`).
The fn endpoint used the operator's local tunnel with pinned TLS certificate
and credentials; the private post config and password were not copied here.
The qualified fn source was commit
`bbf52159dcab19228bd6cd0b855b99dd6d68758d`; its hbox image was
`/tank/fn/gates/qual-bbf52159-20260925/build/images/bbf52159dcab19228bd6cd0b855b99dd6d68758d/fn-host`
(SHA-256 `432622d29a28d59455e01f3e5b426036c5862db21d5f7d1205a9304ab11e3505`,
core SHA `6e569af117ba4afcf52bfd74f2a40ac222ead7701bb0b84bac799c53521bfe9e`).
Its source qualification is recorded in
`/Users/ember/dev/fn/planning/evidence/qual-bbf52159-2026-09-25.md`.

Host op16 returned `proposed-fresh`. The client retained the exact call before
the ordinary signed Mini submit, which confirmed tag-10 transaction
`29137682385895571488715445447079416173021710790114115254805844966599863984553`
as installed at accepted count 3. The client then retained a 399,015-byte
op18 export frame (SHA-256
`90715f594b77d4b77f5a5d10750ce096c9deab83a45a3bf231de0dc4f1aa27eb`).
Its exact decoded 198,808-byte carrier matched the retained signed R
byte-for-byte (SHA-256
`17185686c6a17212251d26bb4e68e91b7f131b20a7b08d36e795669dce2b468c`).
The selected transaction, message ID, source identity, and all four fields of
each origin and outbox receipt matched the independently retained op16 decision
and confirmed Mini outcome.

The publisher durably recorded fn POST attempt 1 before network send. fn
returned the exact final line `240 article received OK`, and the accepted
marker was retained. There was no attempt 2. A same-state `origin-publish`
rerun exited 0 with unchanged attempt, result, and accepted-marker mtimes;
there was still no attempt 2. The read-only fn GROUP result after publication
and after that rerun was A=1, B=1.

A separate, deliberate exact-carrier POST probe outside publisher state then
sent the same signed R once more. fn returned
`441 posting failed; this article is already stored here`; GROUP stayed A=1,
B=1. This probe did not create a publisher attempt 2 and does not represent
recovery from an uncertain POST.

Retained private artifact SHA-256 values:

| Artifact under `publish-state` | SHA-256 |
| --- | --- |
| `outbox-prepare/decision.json` | `82442b107c1f95a89cf86c7aa1ef0d9f74f7df2bfef190a939ee461c1a5618dd` |
| `outbox-submit/call.bin` | `f80ed9071f9d5666f8332400b51f7e5e6fd34c120d9bb34f3733257947bce24b` |
| `outbox-submit/outcome.json` | `d37fec985b4f384b8c6c58ab94ea5a8948e9e0a556e040d600ebe96bda9acf39` |
| `outbox-export.frame` | `90715f594b77d4b77f5a5d10750ce096c9deab83a45a3bf231de0dc4f1aa27eb` |
| `fn-post-attempt-1.json` | `496028580a184f75857697f92647d0d5bcc951e22d472bebd2b4fd7164303497` |
| `fn-post-result-1.json` | `0f1a88878986390279d8985aaf2f75cfb5cff941a192ba53bd3b9c3cbf735730` |
| `fn-post-accepted.json` | `8c825ae42db0ee6003ba67c0d8aadf811bc8671d1d366ce096feae37aef6f909` |

Bounded fn GROUP log: `fn-group-after-publish.log`, SHA-256
`1dbf358203b8fd60bdae7f0fd68929c87a820781867ad5bc0f9b94fc14425abe`.
Same-state repeat summary: `same-state-no-repost.json`, SHA-256
`613c7a07218d655666a24a6125587983e21525c68a1f4c604b452471b2396379`.
Separate duplicate-wire result: `duplicate-post-result.json`, SHA-256
`c214bae8e9233fca66fbbf53f9a0600fb5c74c78c5829d68c3af9ff763ea651b`.
No raw carrier, call, certificate, password, or private publisher state is
copied into this evidence directory.
