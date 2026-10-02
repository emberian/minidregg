# room/private — a room whose content the node stores and cannot read

The kernel checks nothing about what a member says here: every say, tail line and doc
line is sealed on the member's own machine under the room key before it reaches the
socket. The operator sees cell ids, who wrote what at which height, the epochs, each
member's public encryption key, commitments, and sizes in whole 64-byte blocks. Not a key,
not a word. (PRIVACY.md §3.1, §3.6; `native/resource-client/src/roomkey.rs`.)

Run it from your own machine (`mini --remote`, or `mini shell` locally). In the hosted
shell your key is a file on the box, and so is the room key you unwrap with it.

## What the template makes

| cell | law | file |
|---|---|---|
| the room `R` (declared) | `all []`: every member (a holder of `place` under R) bears cells in; capabilities decide reads | `law.room.json` |
| `R-keys` (content, born in R by the founder) | only the founder writes, and only by creating atoms: no edit, no tombstone, no other action. Reads, grants, law installs and revocations are left to capabilities. `@FOUNDER` is replaced by the founder's subject | `law.keys.json` |

`law.keys.json` is the law `Kernel/PrivateRoomKeys.lean` names `keysLaw`;
`keysLaw_refuses_nonfounder_write`, `keysLaw_refuses_edit`, `keysLaw_refuses_tombstone`,
`keysLaw_refuses_non_atom`, `keysLaw_admits_founder_wraps`, `keysLaw_admits_reads` are
what it decides. Because wraps are only ever added, the room's epoch (the largest epoch with a
wrap) never goes backwards; that is the `monotone epoch` PRIVACY §3.1 asked of R, held by
the keys cell instead of a field on R.

One wrap per `(epoch, member)`: atom id `epoch * 2^64 + member`, kind
`inlineObject(schema of DREGG/PRIVATE-WRAP/v1)`, payload = the member's X25519 public key
(32 bytes) then the wrap (104 bytes). Every member may read every wrap; a wrap opens for one
X25519 secret only.

## The verbs

    room new lab --private              the room, k_R^0 (in your encrypted key cache), the keys cell, your own wrap
    whoami                              prints your encryptionKey: give it to whoever invites you
    room invite i1 lab SUBJECT ENC-PUB  the grant (submit i1, publish i1 as ever) + the wrap, written now
         [--past]                       also wrap every earlier epoch you hold (default: the current one only)
         [--i-know]                     invite a hosted subject anyway (see below)
    room kick k1 lab SUBJECT            revoke + rotate to a fresh key + rewrap for everyone else, all submitted.
                                        They keep the past; they get nothing new.
    room rotate r1 lab                  rotate and rewrap without a kick (finishes a kick that stopped half-way)
    room keys lab                       the epochs you hold (local)
    forget lab [EPOCH]                  delete your copies; your client will not unwrap them again
    doc new notes --in lab              a doc in the room: its appends are sealed (edits and links refuse: they would be plaintext)

Every key is in `WORKSPACE/private/keys.cache`, encrypted under `MINI_KEYCACHE_PASSPHRASE`
(Argon2id, 64 MiB). Without the passphrase you see `[sealed under epoch e — you do not hold that key]`.

A member who is not the founder cannot write the keys cell, so cannot give anyone a key: a
member's own invite (re-delegation) gives a grant, and the invitee sees ciphertext until the
founder wraps for them.

## The hosted-librarian flag (B6)

A hosted subject — a friend whose key lives in a session home, hosted Hermes, a bot — has its
encryption key on the box too. `room invite` refuses it into a private room unless you add
`--i-know`, and says why: the room becomes readable on the box, and a hosted Hermes sends what
it reads to its model provider. The operator lists hosted subjects in `/etc/mini/hosted-subjects`
(one decimal per line; `MINI_HOSTED_SUBJECTS` names another file). Default: no hosted librarian.

## What `forget` is and is not

It deletes your client's keys and records the epochs as forgotten so a later read does not unwrap
them again. Your wrap stays in the keys cell (it is append-only), and your encryption key could
still open it, so this is a promise your client keeps, not an erasure, until your key itself is
rotated (PRIVACY row 13). The ciphertext stays on the node and in its backups either way.
