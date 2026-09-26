# Upstream Hermes ↔ Mini content workroom, 2026-09-26

This is a bounded, keyless evidence subset from a fresh Persvati deployment at
`/tmp/mini-workroom-upstream-20260926`. The unforked Hermes ACP worker used a
deterministic loopback chat-completions fixture (`--content-workroom`), not a
real model or provider key. Mini retained the controller custody key and
admitted every content action through the native Lean Host. Parent grain 7301,
tool grain 7302, and content object 8001 belonged to this fresh Store; the
older live 7101 scalar controller was untouched. The provisioner executed
with `WORKROOM_PARENT_TASK=7301 WORKROOM_TOOL_TASK=7302`, source SHA-256
`4648f7222897de69e3454c8b7abad7022719697594c0b987fe24a0bb000ba9c8`.

The first Hermes prompt signed-read the empty page (root
`97349327118568466779609446662939988221287696762075284738918673226692685974561`),
then published `createAtom` text atom 7401 in one grain settlement/content
invocation. `attempt-0000000000000019` installed with acceptedCount 12.
A separate observe-capability-96 read showed the original note, “Workroom
research note: verify the source receipt before reuse.” The second prompt
loaded the **same** Hermes session, signed-read that exact old atom, and
published `editAtom` using its complete observed `before` record.
`attempt-0000000000000043` installed with acceptedCount 20. A further signed
read showed one atom 7401 with the revised text, “Revised workroom note:
Mini accepted the receipt; fn provenance remains a separate check,” at root
`83713759428500027426188977869612645727711005218276351304047157909084634395375`.
The later `resume-read/view.bin` matches the earlier edit read byte for byte
(SHA-256 `634d535e700489267b039c20f2a175a98f1ea1a1955062a3427485e20c71afe4`).

Both create/edit calls installed in Mini **after** Hermes' default 300-second
MCP call deadline, so the upstream worker saw a timeout and the fixture
refused to claim either tool receipt. Neither publication was resent. The
controller was restarted only when its signed parent settlement and journal
were clean. For the third, read-only turn, the private Hermes profile set
`timeouts.mcp.tool_call: 1440` under a fixed 1500-second worker cap; an
upstream config probe resolved exactly 1440 seconds. The source-matched Rust
controller validated that mounted profile before reserve. It performed an
exact-call **lookup**, not a submit, for the retained edit receipt and passed
the historical result into the same Hermes session. The fixture then returned
“Fixture verified the revised text atom through Mini's signed ContentResource
read.” `attempt-0000000000000061` settled the parent at acceptedCount 26.
The final keyless `journal-projection.json` has no child, pending attempt,
hold, settlement due, or unresolved external effect; session/load stayed
verified and edit operation 43 is marked `reported:true`. The create operation
predated that receipt index and is evidenced by its native outcome and signed
content read, not a retrospective client delivery claim.

The exact edit call was exported as `content-edit-package.bin` (250,836 bytes,
SHA-256 `14a69912b57efa8ed735a4a519b3c0872ef73cd9f53dcaae53ffc201bb0927ad`).
An independent selected-bbf Mac Host verified that accepted prefix. The
source-owned strict renderer required the tool 7302 reserved-to-settled leg,
parent 7301 no-op witness, and nonempty content publication 8001, then
authored `R.source` (343,679 bytes, SHA-256
`31e2b475949eb80846d56b96631ab73a05bebbda43ae39ab129a45f1fcbee250`).
This is a proposed fn R origin article; this evidence does **not** claim fn
transport or B Mini admission yet. A fresh fn operator profile must explicitly
allow the larger article and carrier.

Physical scope: the Persvati Mini Host binary SHA-256 was
`faf1f8371f692c404acd5b4c5727bd2019249c1b5f7d1850022789d35f4ee30f`,
native Mini client `3960d33f2eb79116147179de8783d34d0ebd0dc22b238112e818bd248cb8cd91`,
content fixture source `native/hermes-test-provider/src/main.rs` SHA-256
`81b730d8a00153436cffbd069cd71953e9d9d6fb3ec8f6674aebc97047fbe8c9`,
and pinned Mini config SHA-256
`8d886ccb35bab3bebd1da65b23b2a234517f721f24d3d65dd09a4019b0668f96`.
The final controller and worker proxy binary SHA-256 was
`f3b9b160524f55231035833bee4da3d558bca0c53ca62f45ded732fdf521418a`;
the first create turn used SHA-256
`173cb9a6b14aca36f2c232c96e88d54c4355f5be67695b91f05360068b7ee1d6`,
and the second edit turn used SHA-256
`8126b3432c56b040219ef53436a740f123813ee3658888663aa0f0e3df78ff30`.
Those binaries remain in the private run.
The independent Mac selected-bbf Host SHA-256 was
`d94f7eb91ff9c54d1e6c4b46a650e491c0e54ca9b3a1114c5b0dd4ee717269fb`.
No keys, pinned config, full Store, or Hermes transcript are copied here.
`SHA256SUMS` covers every included artifact.
