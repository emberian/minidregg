# Private cells (`PrivateEnvelope/v2`) and private rooms

A private room's content is sealed by the member's client before it reaches the socket. The codec is
`native/resource-client/src/private.rs`; the room-key protocol (wraps, rotation, the cache sync, sealing
stream entries) is `native/resource-client/src/roomkey.rs`; the verbs are `room new NAME --private`,
`room invite … ENC-PUB`, `room kick`, `room rotate`, `room keys`, `forget` (`mini shell`) and
`mini workspace --action room-key|propose --private ROOM|read --private ROOM|tail --private ROOM`. The key
cache is `DIR/private/keys.cache` (`DREGG/PRIVATE-KEYCACHE/v2`, Argon2id + XChaCha20-Poly1305 under
`MINI_KEYCACHE_PASSPHRASE`). There is no kernel change for content: a sealed doc line is an atom
`inlineObject(schema)` holding opaque bytes, a sealed stream entry's payload is the envelope, and laws see only
counts and byte sizes.

**Envelope.** `"DREGG/PRIVATE-CELL/v2" ‖ epoch:u32 ‖ commit:32 ‖ nonce:24 ‖ ct`, where
`commit = cSHAKE256("DREGG.PRIVATE-CELL.COMMIT/v1"; room, cell, address, epoch, r, v)`. `r` is a 32-byte blinder
sealed inside `ct = XChaCha20-Poly1305_{k_R^epoch}(r ‖ len ‖ v ‖ 0…)`, with AAD = frame, room, cell, address, epoch,
commit. The zero padding makes the WHOLE envelope a multiple of 64 bytes (`envelope_len`): values of 0–59 bytes
are 192, 60–123 are 256, and so on. `address` is the atom id for a doc line and the stream sequence for an entry.
A v1 envelope (133 + 64k bytes) refuses to decode.

**Room keys.** `k_R^0` is drawn by the founder's client; every later epoch is drawn fresh at a kick. The node
holds wraps only: the room's `keys` cell (born in the room; law `deploy/shell/templates/room/private/law.keys.json`,
theorems `Kernel/PrivateRoomKeys.lean`) has one atom per `(epoch, member)` at id `epoch·2^64 + member`, payload
= the member's X25519 public key ‖ the wrap (ephemeral X25519 → cSHAKE KEK bound to room, epoch, member and both
public keys → XChaCha20-Poly1305). A friend's X25519 key is `cSHAKE256("DREGG.CLIENT.ENC/v1"; seed)`, from the same
seed that signs (`mini enc-public --secret KEY`, or `whoami` in the shell).

**The operator cannot see** any sealed value, any room key, or which value a commitment hides (the commitment is
blinded). It cannot move an envelope to another cell, address or room, or swap its commitment, without a member's
open refusing.

**The operator still sees** cell ids, atom ids and stream positions, epochs, commitments, each member's public
encryption key, and each envelope's size in 64-byte blocks. It also sees when every write happened, which subject
signed it, and membership, because every capability's lineage is in the authority cell (PRIVACY §3.6). A member
reads everything its keys open, including epochs from before it was kicked, and anyone who kept a past epoch's key
can still read that epoch.

**Key loss (the text printed at `keygen`, `private::KEYGEN_NOTICE`):**

> This key is the only copy. It signs as you and opens your private rooms.
> If you lose it there is no recovery: you enroll a new subject and are re-invited.
> Room content comes back by re-wrap at the current epoch; older epochs come back
> only from a member who kept them. Your old posts stay under the old subject.
> Escrow is off. `--escrow-to-sponsor @SPONSOR-ENC-PUB --escrow-subject SUBJECT` writes your seed encrypted
> to your sponsor, which lets your sponsor sign as you.

The sponsor opens an escrow with `mini escrow-recover --escrow PUBLIC.escrow --sponsor-secret KEY --subject SUBJECT
--secret NEW-KEY`; only the sponsor's X25519 key opens it, bound to the subject.
