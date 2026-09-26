# Hosted peer continuation: A reconciled; B's stale write exposed a retained hold

This keyless checkpoint continues the [first two hosted writes](../2026-09-26-hosted-peers-first-two/README.md)
in the same Mini Store and the same separate Hermes A/B sessions. It records
one successful A edit and one **incomplete** B stale-root workflow. The B
workflow must not be counted as a completed retry/recovery test.

After B's note at root
`35864103203070487825209116823705667097941681304399420615738069163522242632150`,
A loaded retained Hermes session `a22070a4-df24-4c34-89e0-1d0772b5a995`
(`loadVerified:true`), signed-read that version, and submitted one
`editAtom` on content object 8001 / atom 7401. Native tool attempt 58 was
confirmed with transaction
`14358396813081949732388176001886310974782792329627781586967388820161585883737`,
event
`80963629866777002407198942306886379066984354677392772720811432218165939994558`,
acceptedCount 35, and image boundary
`65349467367451698574133643431191635660833317671093324124006569744634048789906`.
Its parent settlement attempt 63 confirmed acceptedCount 37. An independent
signed A cap-96 query returned one atom 7401 with text “Peer A reconciled the
note with the latest peer review.” at root
`29137308833432958150683493573484108359150772114323482422807431380493295318727`.
The signed `view.bin` SHA-256 is
`fe2c76de6077824c35add5fafb04cdf25ea6f3dc98f2f7a0c1b6b40b271598e5`.
A's selected journal projection is clean after this turn. The model-visible
success was a task/root tool acknowledgement; Mini retained the exact native
receipt in its journal.

B loaded its distinct retained Hermes session
`05e9ccf7-73d1-404f-8702-dcc60fd4bdf2` and reused the **earlier signed**
A root
`48493925927325687515524431001378288182086419757969404647362684922014763241255`
for a stale `mini_publish` attempt. Tool reserve attempt 42 confirmed
acceptedCount 42. Tool settlement attempt 44 reached native Host preparation,
which refused with encoded
`Minidregg.Kernel.DeclaredResourceController.Reject.staleTarget`.
The selected exact model-visible MCP error is in
`b-stale/model-visible-tool-error.txt`; its encoded native outcome decodes to
`invocation preparation: ... Reject.staleTarget`. Attempt 44 has a retained
signed observation but **no `call.bin`, `outcome.bin`, `outcome.json`, or
`reply.frame`**; `attempt-files.txt` lists its directory contents. This is a
pre-submit stale-target refusal, not an accepted B content mutation and not a
transport deadline.

The old runtime nevertheless marked tool attempt 44 `uncertain:true` and
retained its reserve-2/charge-1 tool hold. The fixture did not recognize the
hex-encoded refusal as an explicit stale-target tool error, and correctly
declined to call its own stale test successful. B's parent settlement attempt
46 separately confirmed acceptedCount 43. Its worker and connector exited,
but `b-stale/journal-projection.json` still shows tool attempt 44 and the
hold; no retry was issued. An independent signed B cap-98 query after the
refusal returned the **same bytes and SHA-256** as A's post-edit `view.bin`,
at the same root and with the same A text. Thus B's stale publication did
not change the room. Recovery and zero-charge hold release remain open work.

Source/binary scope: native Host SHA-256
`4bb72e1e984de413ee0065d7d229dbe0217bf980b4563ba26dc85ee38ed59c65`,
Mini client SHA-256
`128bd81cb5876f2cf0071767b8022b5d961ce94956cfd2d550e7d34fc54e7703`,
grain runtime SHA-256
`e17ad58b73b43c611bdb6fa22d5fe42a56f75720889fb0901c81337d11eb763f`,
and peer fixture source SHA-256
`99649355eba0042b31096761f6c5e3dc865e0e3ab194d056bbfcee0a56dcfd8c`
with Linux ELF SHA-256
`1e399d6c79fe2cdc1edda38accd2a8d799c6aded6a8469fdc9bea884c1cccc57`.
The worker wall cap was 1500 seconds and mounted Hermes MCP tool timeout
1440 seconds; the native refusal occurred during prepare before either cap.
No custody key, private config, full Store, or Hermes transcript is copied.
