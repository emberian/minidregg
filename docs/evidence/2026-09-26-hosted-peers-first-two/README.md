# Two hosted Hermes peers in one Mini content room: first two writes

This bounded, keyless checkpoint covers the first two prompts of a fresh
shared Mini Store. It does not claim the later reconcile/stale-root sequence.
Two separate unforked Hermes ACP workers used deterministic local loopback
chat-completions fixtures, with no model or provider key. Controller 7801 and
tool 7802 ran as subject 7/8; controller 7803 and tool 7804 ran as subject
9/10. The two workers had distinct homes, runtime roots, cgroups, session
IDs and loopback provider ports, while both used native content object 8001
in the **same** Mini Store. The provisioner's signed authorized empty read
root was
`97349327118568466779609446662939988221287696762075284738918673226692685974561`.

| Stage | Native accepted publication | Independent signed content read |
| --- | --- | --- |
| A `workroom-a-create` | Tool 7802 attempt 20 confirmed: transaction `102880997551007654483402307768314486722647903662184607915090640480056943725114`, event `107848528897897700198443394989789666395004609712696620424157089603472949403164`, acceptedCount 15, image boundary `4695009488064504610488676458937062718957562296109476944507075623067101219274`. Parent settlement attempt 25 confirmed. | A observe cap 96 showed exactly atom 7401, text “Peer A research note: review source receipts before sharing.” Root `48493925927325687515524431001378288182086419757969404647362684922014763241255`. |
| B `workroom-b-review` | Tool 7804 attempt 20 confirmed: transaction `91584406951252096426343980097823765581993847451754431567186572108196622647305`, event `2130796006310182160631371902657327534093710263064086308136635274172395065351`, acceptedCount 23, image boundary `91625779509469758577613274978405724820365207977867762207140257502836143236357`. Parent settlement attempt 25 confirmed. | B observe cap 98 signed-read A's root, then after its own edit showed exactly atom 7401, text “Peer B reviewed the note and added cross-check evidence.” Root `35864103203070487825209116823705667097941681304399420615738069163522242632150`. The atom still records original creator subject 8/capability 95. |

The exact accepted calls and native `outcome.bin`/`outcome.json` are under
`a-create/attempt` and `b-review/attempt`; each signed read preserves
`signed-observation.bin`, `view.bin`, and its decoded `view.json`. The two
call SHA-256 values are
`619c4692a8f739afe941759d4670212507a8e44fe203f9371527081c175eabd9`
and `e628809ea221c70b852987dec495f8298cba98330bf8ce81e674f60590abfcf2`.
The signed read view hashes are
`9c9fbc63dce6261639ca2e1761acc1abbb4118ac6b8c1273a0b593886534f05d`
and `e4e8a21ba40c90758249e7c466b2872cbfd8a8edaea7862babc4b8da9e712cf0`.
B's keyless journal projection shows no child, pending attempt, hold,
settlement due, or unresolved external effect after its prompt; retained
Hermes session ID is `05e9ccf7-73d1-404f-8702-dcc60fd4bdf2`. A's retained
session ID is `a22070a4-df24-4c34-89e0-1d0772b5a995`; its first turn
also settled clean before the subsequent turn began.

The fixture's first binary logged `peer receipt`, but its model-visible
`mini_publish` success contained a task/root **tool acknowledgement**, not
the original four-field native receipt. Mini retained the exact native
receipt in the controller journal and later projected it as historical
recovery data. This evidence uses the native outcomes above for the receipt
claim. The separately retained parent outcomes show each grain settling.

Physical scope: native Mini Host SHA-256
`4bb72e1e984de413ee0065d7d229dbe0217bf980b4563ba26dc85ee38ed59c65`,
native Mini client SHA-256
`128bd81cb5876f2cf0071767b8022b5d961ce94956cfd2d550e7d34fc54e7703`,
pinned Mini config SHA-256
`9ee6274296b27ebd8024fad83100e73bcb1d9ba2ed072f9b43baf7f8e17771f4`,
grain runtime SHA-256
`e17ad58b73b43c611bdb6fa22d5fe42a56f75720889fb0901c81337d11eb763f`,
and initial peer fixture source SHA-256
`75cbcee38d51ab304e69b1da2ca30eb2fe655d0bacf36a22de6d632c25e463c4`
with Linux ELF SHA-256
`8a6b81c6d830c67483e36cd083470a34bc3b0017aa6fff1ec5118b2d899ab2ec`.
No custody key, worker config, full Store, or Hermes transcript is included.
