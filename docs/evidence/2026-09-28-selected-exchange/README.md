# Selected Mini content over isolated fn, 2026-09-28

This is a bounded construction run. All Mini Stores and fn Stores named below
were freshly made under the private hbox directory
`/tank/dregg-preview/mini-selected-exchange-20260928-r1` (mode 0700). No
preserved fn node or Store was written. The Mini source object had selected
atom `7401` and a distinct unselected atom `7402`; the complete 400-byte
release packet contains the selected text once and the unselected text zero
times. The published MIME body decoded exactly to that packet. This checks
one selected release, not general absence of all private-history disclosure.

## Pinned images and input

| Item | SHA-256 / identity | Qualification |
| --- | --- | --- |
| Mini Host at `host-2721253` | `f62c716885d8f9258750da70113afc8d4086907a2cdbc1c11a8a5e3c5043bdcd` | Source/build `2721253`, manifest `/home/ember/build/minidregg-2721253-evidence/build-r1/manifest.txt` on persvati. |
| Mini client used for first prepare/publish | `b54436ed96cda71e9ed45d6c8c3af1e5d95af9bea089de23b14a407bb5eed641` | Retained in `exchange-r1/pin.json`; client WIP image, not a qualified release. |
| Qualified fn format-8 launcher | `432622d29a28d59455e01f3e5b426036c5862db21d5f7d1205a9304ab11e3505` | `/tank/fn/gates/qual-bbf52159-20260925/build/images/bbf52159dcab19228bd6cd0b855b99dd6d68758d/fn-host`; this is older than current format10. |
| Installed fn format-10 launcher/core | `dcc655e610ae67c638a8504cc8030acfb6645ac0fb0b418b4d74fb8f9159bd71` / `882cd36a59224351989e790e233a68f82e0b2e5d1923b0a0702a0e81aaeb1b89` | Source `a3553e6b4a230515dc661fe2e175be4a90400805`, a current development release on a **separate freshly initialized Store**, not a qualified Mini/fn integration image. |
| Prepared owner packet / fn article | `7cb222a733ad6dab12603423f67b0511add5ed5ce8d66073a4d403600cbf791d` / `907eaf0a09194faf2ed60b9ab7dc555832f88438bb6c8c5523b2f81091e9e830` | Exact bytes retained privately in `exchange-r1`. |

## Observed boundaries

1. `selected-exchange prepare` passed with a signed current source resource
   view and exact atom payload. It performed no Mini/fn publication. Then
   `publish` admitted source event14 with a confirmed Mini receipt
   (`transactionId` `36496709547442588597974462141791752561995620370522487088917874529742433421790`)
   and fn answered `240 article received OK` on the qualified format-8
   isolated node. An fn response alone is not recipient admission.
2. `receive` refused before recipient event13. The retained qualified-format8
   poll report is 1,219 bytes, SHA-256
   `23b4f7d8f3eee36033ea4aad216dbe3360e839045f3a42ae6dd9737a8dc7734d`,
   and starts with encoded `fn-r`. Native `consumer-project` requires `fn-e`
   and returned `fn-consumer-project-refused-v1 codec`. The Host retained
   cursor/report and produced no recipient ingress or receipt.
3. On the separate current-format10 Store, protected NNTP accepted the **same
   exact event14-admitted article** with `240 article received OK`. A direct
   Host poll again refused at the same boundary: 1,369-byte report SHA-256
   `568e75b98319c68bf7f76c6e0bc6bbb59cc71f6eba98d8903ae4baa8d47bc39b`
   begins `fn-r`; `consumer-project` returned `codec`. This is a transport and
   receiver compatibility probe, not a second successful full client publish.
   Current fn `consumer-article --json` does decode the `fn-r` report as a
   stored Message-ID and article. The 1,058-byte stored article has a 225-byte
   injection prefix and ends with the exact 833-byte owner-authored article.
4. An exact owner packet wrapped for the **wrong recipient target root** `1`
   was submitted to the first isolated recipient Mini. It returned a retained
   `type: refused`, `phase: admission`, with no event13 receipt. The refusal
   JSON SHA-256 is
   `82bd41a677c72c6884c143b207d1b52b279d3d6e0f12bd1fe1a79bb6e23e265e`.

The first client contract SHA-256 was
`fdaf1e1622d5bf8cbaafeaafa39a30bf79d2f7839e8631b65e11b0918cf72040`.
Retained private artifacts remain in `exchange-r1`, `poll-format10-direct`,
and `negative-wrong-root` under the hbox directory above. The format10 node
and Mini recipient use independent Stores and domains but the fixture uses
the same generated owner key in both. It therefore does not demonstrate an
independently credentialed friend receiving or a complete Gate C result.

The follow-up Mini `selected-release-fn-legacy-poll` path explicitly uses fn's
ACL2 `consumer-article` decoder over an authenticated local poll. It binds the
stored article and Message-ID to the exact canonical owner release, then lets
recipient Mini event13 check the owner signature and current recipient law.
It deliberately makes **no fn-e verdict, event17 coverage, or fn cursor ACK
claim**.

## Successor Host live transport-only run

The source-matched successor Mini Host `e22d16b` qualified with all 363 Lean
modules and native artifact readback. Its ELF SHA-256 is
`723940446d3e0256bd446b07ca8d67ea9d67295d8c7cc78e08bb2487ffbe3db2`;
its build manifest is
`/home/ember/build/minidregg-recovery-20260928/native-e22d16b/build-r3/manifest.txt`
on persvati, SHA-256
`862e17fcf0a462bdad6b830cd3a46e13801af1a2339a1ee9e41f1ef552d24afb`.
The Mini client was the separately retained release binary SHA-256
`b41fd49e664892db27f4522ca2587ac07b510fb85174dbfa5dc38c8d314ce381`,
using selected-exchange source SHA-256
`3a9fce0809c94aa0c568092c0b4db00dd84cab61f020bea29e494c1303b59dab`.
The private contract SHA-256 was
`da3ff44fe4e5038afad011240bb576212b78602b4f96593cf0d908b9fb646635`.
This ran against **another** newly initialized format10 fn Store,
`fn-format10-final`, with consumer committed ACK 0 and only two setup records
before posting. The final Store used the same pinned current fn launcher/core
source above, with its own TLS certificate, credentials, port 11216, history,
incarnation and consumer scope. Its scope file SHA-256 was
`9cd823130f9d63bf5de91cdba2404befc18ec50aeeeec909dbf51d09b77b77e5`.

1. `prepare` passed on a fresh selected source signed query and exact atom
   payload. `publish` then confirmed source event14 transaction
   `95905337985452104475027332300665331168067911460154463512705376065552477668882`
   and received `240 article received OK` from the fresh format10 fn Store.
   The exact owner packet SHA-256 was
   `a9393487a5ba583774029fd5d204b1561e585eda3382ddd0721a6771b3bca610`;
   article SHA-256 was
   `78cc55f2a55ac779ecb2e23483e9d727e5ed05abdb13c8b399fccfd4e40dcea7`.
2. `receive-transport` used Host `selected-release-fn-legacy-poll`. Fn's
   authenticated local poll returned cursor position 3 and the exact `fn-r`
   report SHA-256
   `6382af43b15133b1a62738c738a0ab1de56b25043da173295bf68c451dc9a588`.
   Native ACL2 `consumer-article` decoded the Message-ID and 1,058-byte stored
   article (SHA-256
   `18c66eedda1a0d376d11531cc191eb04af695e68775632bab9bc497156daec41`).
   It had a 225-byte injection prefix and exact 833-byte selected article
   suffix. The Host produced the exact 400-byte owner packet and recipient
   ingress, **without fn-e verdict or ACK**.
3. Recipient Mini event13 returned a confirmed **installed** receipt, tx
   `101971813110487125665168039513823946124091771120143855328537607864473094872435`,
   event
   `80622145517364409334342446058879448571284405408455098270505605508518790276609`,
   accepted count 3, image boundary
   `10945663206964684424970494887224667245384672572109678566744673645790790838624`.
   Reentering `receive-transport` performed the retained exact lookup and
   returned `replayed` with all four receipt fields unchanged; there was no
   second event13 submit.
4. A fresh separately authorized signed recipient query after the service
   stopped returned exactly one schema-11 inline object atom at that event13
   transaction ID with payload equal to the retained packet. Its signed
   observation SHA-256 was
   `cfa0a4cae0f0b46d6012d2444cb5cb42103f6ac237d15f3adedd77fdbb0cc667`.
   The original pinned client's orchestrated `verify-transport` phase had a
   one-word intent-kind bug (`json` instead of `intent`) and refused before
   reading. Shared client source was corrected and passed `cargo check`,
   selected-exchange nextest 5/5, and clippy `-D warnings`, but its changed
   binary cannot be silently substituted into the pinned attempt. The signed
   readback was therefore performed with the original pinned client through
   its ordinary query command. Orchestrated `verify-transport` remains
   untested after the fix.
5. A read-only negative on the same fn Store altered the expected article's
   Subject header in a separate private file. The qualified Host legacy poll
   refused `fn stored article lacks exact selected owner source suffix` before
   producing packet/ingress or submitting Mini event13. The earlier wrong-root
   admission refusal was on the first isolated recipient fixture, not this
   final recipient Store.

The final retained files are privately at `exchange-format10-final` and
`negative-tampered-article` under the same hbox root. These results establish
one selected public content atom through real fn transport to recipient Mini
admission and exact signed readback, with a same-attempt duplicate and two
bounded refusals. They do not establish a separately credentialed friend,
fn event17/ACK for legacy `fn-r`, or application installation from the packet.
All three test fn user units and the isolated recipient user units were
stopped after evidence capture; their reported states were `inactive`.
