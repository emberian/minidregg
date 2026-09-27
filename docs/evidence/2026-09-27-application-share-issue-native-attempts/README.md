# Share-issue native attempt checkpoint

No share ticket was submitted or issued in these attempts. The frozen native
Host was `/home/ember/build/minidregg-overnight-20260927-success-prefix-final-evidence/minidregg-host-ebddd8e-prefix-r2`, SHA-256
`65b9877366acf2cb55c575cbd9cdde72c9476370434c8e328c851129799619ef`
(certified manifest SHA-256 `42653cd45cbd951c24a860cfdd1850aaf89213aa54378245278061a7af267dcc`).
The initial Mini client was the independently certified exact-ebddd8e binary
`/home/ember/build/minidregg-ebddd8e-helper-evidence/bin/mini-ebddd8e`, SHA-256
`ea24a5efdc5807f4bee6acd349a44583c0ca5760c6675b98fb5a5a34c2e5eca4`.
SQLite Store and signature helpers were respectively SHA-256
`ad03aede839259c1884383fc97f141a3fe106ba2f2cbae0df6f7916676fe193f`
and `c84004123ae6f02654cb6749e4105e351199618aaefce5755a2a0bb10bd0892b`.

The retained private source/Store root is
`/tmp/mini-share-issue-ebddd8e-fixture-20260927` on Persvati. Its
`source/source-sha256.txt` is copied here. This record gives exact sources and
failure points, not a green share-issue verdict:

| Attempt | Result | Native effects |
| --- | --- | --- |
| `run-r1`, launcher SHA-256 `1b1863698cfa14a8035d85e002adcee7e05db97b71739b0c703826f10bab3c7d` | Fresh app and session native births, signed readbacks, historical replay and reopen **passed**. The outer positive-base wrapper then read `base/base/workroom` instead of `base/workroom` and exited 2. | App/session births happened in the private fresh Store. Positive tariff was independently checked as 1 in operator and genesis files; retained input and private overlay hashes rechecked. No share request was authored. |
| `run-r2`, launcher SHA-256 `62fcc27cf3c271af4dfaffeddacb9a95390e93a42d8f7561dbceb593f3d907c2` | Used the known r1 base, authored a request/preview plan and signer approval. The public participant socket correctly refused op32, but the fixture expected an obsolete error string and exited 1. | No private plan, signed ingress, or op28. |
| `run-r3`, launcher SHA-256 `944ec492845af6e64871e12425fabfb1ed975dd1f01d4a435d6ee54029fc2e98` | Public op32 refusal passed. An alternate low-balance payer's plan was refused and the before/after full Store image matched. The next custody test failed before request authoring: the client tried source `author/inspect` op7/8 through its operator socket, which rightly accepts only private checked routes. | No private op32/33, signed ingress, or op28. The shortage refusal alone does not isolate insufficient balance from that payer's authority. |

The r1 and r2 fixture-path/assertion repairs are committed. The r3 production
client repair is committed as `aed69d2`: source authoring, inspection, and
signature-list encoding now invoke the same pinned Host executable directly,
while op32/33 and submit/lookup remain on the private operator socket. Its
`native/resource-client/src/share_issue.rs` SHA-256 is
`dd6a257f4e5befdc735e3896398872a3ce92d23a7c13fc226b6fccb4c29d8e71`.
The focused child-process regression sets the global socket to a nonexistent
path and proves the source helper still calls the selected Host. An isolated
Persvati source copy and target ran
`cargo nextest run --manifest-path native/resource-client/Cargo.toml -p minidregg-resource-client -E 'test(/source_helper_ignores_operator_socket/)' --locked`:
**1 passed, 63 skipped**. The complete log is copied here, SHA-256
`133b132f556c853381df6bd49efaecd3293dd6cf46df59453aedcd394652eb99`.

The next native ticket attempt must use a newly certified client containing
`aed69d2`, the same certified Host, and the unchanged pre-share r1 base. A
version-0 ticket from this positive-fee fixture will prove only fee, Book,
receipt and recovery behavior. A dispatch-capable GitWeb ticket requires a
separate accepted version-1 package INSTALL and current manifest binding.
