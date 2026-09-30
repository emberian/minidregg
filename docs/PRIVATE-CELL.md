# Private cells (`PrivateEnvelope/v1`)

A private cell is a content cell under a room whose text atoms the client seals before they reach the
socket. The code is `native/resource-client/src/private.rs`, reached by `mini workspace propose … --private ROOM`
and `mini workspace read … --private ROOM`. The key cache is `DIR/private/keys.cache`, and its passphrase comes from
`MINI_KEYCACHE_PASSPHRASE`. There is no kernel change: the atom is `inlineObject(schema)` holding opaque bytes, and
content laws see only counts and byte sizes (`Kernel/ContentResource.lean`, `project`).

**Envelope.** `"DREGG/PRIVATE-CELL/v1" ‖ epoch:u32 ‖ commit:32 ‖ nonce:24 ‖ ct`, where
`commit = cSHAKE256("DREGG.PRIVATE-CELL.COMMIT/v1"; room, cell, atom, epoch, r, v)`. `r` is a 32-byte blinder sealed
inside `ct = XChaCha20-Poly1305_{k_R^epoch}(r ‖ len ‖ pad64(v))`, with AAD = frame, room, cell, atom, epoch, commit.
Room keys are wrapped per member (ephemeral X25519 → cSHAKE KEK → XChaCha20-Poly1305) in one `DREGG/PRIVATE-KEYS/v1`
JSON record per epoch. A friend's X25519 key is `cSHAKE256("DREGG.CLIENT.ENC/v1"; seed)`, from the same seed that signs.

**The operator cannot see** any sealed value, any room key, or which value a commitment hides (the commitment is blinded).
It cannot move an envelope to another cell, atom or room, or swap its commitment, without a member's open refusing.

**The operator still sees** cell ids, atom ids, epochs, commitments, and each value's size in 64-byte classes
(0–64, 65–128, …). It also sees when every write happened, which subject signed it, how many atoms each write made,
and membership, because every capability's lineage is in the authority cell (PRIVACY §3.6). A member reads everything
its keys open, including epochs from before it was kicked, and anyone who kept a past epoch's key can still read that epoch.

**Key loss (the text printed at `keygen`):**

> This key is the only copy. It signs as you and opens your private rooms. If you lose it there is no recovery:
> you enroll a new subject and are re-invited. Room content comes back by re-wrap at the current epoch; older epochs
> come back only from a member who kept them. Your old posts stay under the old subject. Escrow is off.
> `--escrow-to-sponsor @SPONSOR-ENC-PUB` writes your seed encrypted to your sponsor, which lets your sponsor sign as you.
