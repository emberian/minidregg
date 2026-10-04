# room/private — a room whose content the node stores and cannot read

**devnet quality; privacy not audited; founder-key pin is trust-on-first-use via the operator unless verified out of band.** Full design and threat model: `docs/PRIVATE-CELL.md`.

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
| `R-keys` (content, born in R by the founder) | regions by atom id. WRAPS and RELEASE records (high half of the id nonzero): only the founder writes, only by creating atoms -- no edit, no tombstone, no other action. Each subject's ENCRYPTION-KEY RECORD (atom id = its subject number): only that subject writes it, one create or edit. Reads, grants, law installs and revocations are left to capabilities. `@FOUNDER` is replaced by the founder's subject | `law.keys.json` |

`law.keys.json` is the law `Kernel/PrivateRoomKeys.lean` names `keysLaw`;
`keysLaw_refuses_nonfounder_wrap`, `keysLaw_refuses_foreign_record`, `keysLaw_refuses_wrap_edit`,
`keysLaw_refuses_tombstone`, `keysLaw_refuses_non_atom`, `keysLaw_admits_founder_wraps`,
`keysLaw_admits_own_record`, `keysLaw_admits_reads` are what it decides. The law does not decide which epoch is current: each client does, from founder-signed
certificates checked under its pinned founder key, and it never accepts a lineage below the head it retained.

A wrap of epoch `e` for member `m`, addressed to `m`'s key of generation `g` (the key epoch of
the record it went to; 0 for the key given at invite): atom id `(e + 1)·2^96 + g·2^64 + m`, kind
`inlineObject(schema of DREGG/PRIVATE-AUTH-WRAP/v2)`, payload = the member's X25519 public key, the wrap
(104 bytes), the member's keys-grant capability id (8 bytes, 0 for the founder), the founder-signed
epoch certificate (192) and delivery signature (108). Its RELEASE record (written one turn earlier,
commitments only): atom id `((2^30 + 1 + e) << 96) | g << 64 | m`, schema `DREGG/PRIVATE-ROOM-RELEASE/v1`.
A member's record: atom id `m`, kind `inlineObject(schema of DREGG/PRIVATE-ENC-KEY/v2)`, payload = key
epoch, X25519 key, room, keys cell, the member's signing key and its signature (148 bytes); the
founder accepts it only under the signing key it pinned from the member's declaration. A second wrap to the same key is the same atom and refused; a re-wrap to a
member's newer key is a new atom.

At invite the founder also delegates `observe, mutate` on the keys cell alone to the invitee: the
law confines it to the invitee's own record. `rotate-key` publishes the member's new encryption key
there (its X25519 key comes from the seed, so a signing-key rotation changes it) and keeps the old
secret in `KEY.enc-ring`, so past epochs stay open; the founder's next rotation wraps to the record.

## The verbs

    room new lab --private              the room, the keys cell, your pinned founder key + fingerprint, the genesis release to you
    mini workspace --action room-key --op recipient-record --room-id R --keys-cell K --key-epoch N --founder-key F
                                        (a member) pin the founder key you were given directly, and print your
                                        signed declaration: give it to the founder directly
    room invite i1 lab SUBJECT @DECL    the grant (submit i1, publish i1 as ever), pin SUBJECT's signing key,
                                        then the release records, the readback, and the wrap
         [--past]                       also wrap every earlier epoch you hold (default: the current one only)
         [--i-know]                     invite a hosted subject anyway (see below)
    room kick k1 lab SUBJECT            revoke + rotate to a fresh key + rewrap for everyone else, all submitted.
                                        They keep the past; they get nothing new.
    room rotate r1 lab                  rotate and rewrap without a kick (finishes a kick that stopped half-way)
    room register g1 lab                (a member) publish my current encryption key as my record
    room rewrap w1 lab SUBJECT          (the founder) wrap SUBJECT's past epochs again to its record
                                        (its record must verify under SUBJECT's pinned key; a member whose
                                        signing key changed re-declares: room-key --op pin-member --replace true)
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
