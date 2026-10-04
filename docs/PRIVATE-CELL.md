# Private cells (`PrivateEnvelope/v2`) and private rooms

> **Devnet quality; privacy not audited.** The protocol below is implemented and unit-tested against a fake node and
> pinned by independent known-answer vectors; no third party has reviewed it, and the devnet node is one validator
> that is also the operator. Read the residuals in "The operator still sees" before relying on it.

A private room's content is sealed by the member's client before it reaches the socket. The codec is
`native/resource-client/src/private.rs`; the room-key protocol (wraps, rotation, the cache sync, sealing
stream entries) is `native/resource-client/src/roomkey.rs`; the verbs are `room new NAME --private`,
`room invite … DECLARATION`, `room kick`, `room rotate`, `room transition`, `room keys`, `forget` (`mini shell`) and
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

**Status: devnet quality; privacy not audited; founder-key pin is trust-on-first-use via the operator unless verified out of band.** Design: `docs/PRIVATE-ROOMS-DESIGN.txt` (2026-10-04).

**Where an envelope is sealed.** Only at a stream position (`roomkey::seal_for_room`, the signed view's
`nextSeq`): a position holds one entry forever, so no room-key envelope is ever re-sealed at an existing address.
Legacy room-key doc lines are read-only (`private::legacy_content`: structure and a strike that keeps the exact
ciphertext); fresh private document text goes through protected-document audiences.

**Room keys.** Each epoch's key is drawn fresh by the founder's client (never derived). The node holds wraps only,
in the room's `keys` cell (law `deploy/shell/templates/room/private/law.keys.json`, theorems
`Kernel/PrivateRoomKeys.lean`): a WRAP of epoch `e` for member `m` at generation `g` is atom `(e+1)·2^96 + g·2^64 + m`,
payload = recipient key id (32) ‖ wrap v3 (1192 bytes, below) ‖ keys grant ‖ the epoch certificate (192 bytes) ‖ a
delivery signature (108 bytes). Every
wrap is preceded, in an earlier turn, by its RELEASE record at `((2^30+1+e)<<96) | g<<64 | m`: a founder-signed
commitment to the wrap's exact bytes, its certificate, the digest of the recipient's signed record and its grant.
A friend's encryption identity is a hybrid pair derived from the one signing seed: X25519 =
`cSHAKE256("DREGG.CLIENT.ENC/v1"; seed)` and ML-KEM-768 from the FIPS 203 seed
`cSHAKE256-XOF("DREGG.CLIENT.KEM-SEED/v1"; seed)`. A wrap (v3) is ephemeral X25519 ‖ ML-KEM-768 ciphertext ‖ nonce ‖ box,
under one cSHAKE256 key over BOTH shared secrets and the full transcript (room, epoch, member, both ciphertexts, both
public keys), so it is secure if either primitive survives: a recorded wrap is not harvest-now-decrypt-later exposed.
Older record/wrap/keyring versions refuse by name (re-found the room). A member's signed key record (v3, 1333 bytes)
carries both public keys and a custody byte: whether the member's own signing key is a file on a shared (hosted) box.

**The founder's key can move without a re-pin.** `room transition ID ROOM NEXTFILE` (before `rotate-key`) writes a
record signed by the old AND the new founder key into the keys cell; `rotate-key` refuses a founder until it has;
every client verifies the chain from the key it pinned (design §7).

**A private room is never mirrored to Discord.** `tail --json` states `private` on every line and the mirror
refuses a feed that says private or says nothing (design §8).

**Authority: pins, not what the node serves.** Every certificate, wrap and release must verify under the room's
PINNED founder key (`DIR/private/room-founder-ROOM.json`), and every recipient record under the founder's pin for
that member (`room-members-ROOM.json`, from the member's signed 148-byte declaration). Certificates form one chain
from a genesis certificate, each epoch strictly above its parent; the client retains its head
(`epoch-head-ROOM.json`) and refuses any served lineage below it, forked from it or empty. A member pins the founder
key with `room-key --op recipient-record --founder-key` (or `--op pin-founder`): that is trust on first use through
whatever channel carried the key — the operator, unless the member compares the printed fingerprint with the
founder directly. Re-pinning is explicit (`--replace true`).

**Release ordering.** A wrap of an already-used key discloses it the moment it leaves the client, whatever the node
later refuses. So the founder's client retains a draft (`private/room-releases/OP/`), writes the release records
(turn 1, commitments only), reads the keys cell back — records byte-exact, every recipient's record unchanged, the
head unchanged, every recipient still a member — and only then writes the wraps (turn 2). A release that fails
readback, or that a newer release of the room supersedes before disclosure, is DEAD: its ciphertexts are never sent,
its key never enters the sealing cache, and its epoch is burned (the next one is drawn above every epoch a release
ever named).

**The operator cannot see** any sealed value, any room key, or which value a commitment hides (the commitment is
blinded). It cannot move an envelope to another cell, address or room, or swap its commitment, without a member's
open refusing, and it cannot mint an epoch or a wrap without the founder's key.

**The operator still sees** cell ids, atom ids and stream positions, epochs, commitments, each member's public
encryption key, and each envelope's size in 64-byte blocks. It also sees when every write happened, which subject
signed it, and membership, because every capability's lineage is in the authority cell (PRIVACY §3.6). A member
reads everything its keys open, including epochs from before it was kicked, and anyone who kept a past epoch's key
can still read that epoch. **An active operator can still** withhold: keep a member that has not yet seen a newer
epoch on the old one (the pre-kick view), since a single server offers fork consistency at best; and hand a
newcomer a substituted founder key if the fingerprint is never compared. **Post-quantum for recorded wraps**: a recorded wrap is
hybrid X25519 + ML-KEM-768 (design §6); the signatures that authenticate founder, certificates and releases are Ed25519,
so only the confidentiality of recorded wraps is post-quantum, not the authority of future ones.

**Key loss (the text printed at `keygen`, `private::KEYGEN_NOTICE`):**

> This key is the only copy. It signs as you and opens your private rooms.
> If you lose it there is no recovery: you enroll a new subject and are re-invited.
> Room content comes back by re-wrap at the current epoch; older epochs come back
> only from a member who kept them. Your old posts stay under the old subject.
> Escrow is off. `--escrow-to-sponsor @SPONSOR-ENC-PUB --escrow-subject SUBJECT` writes your seed encrypted
> to your sponsor, which lets your sponsor sign as you.

The sponsor opens an escrow with `mini escrow-recover --escrow PUBLIC.escrow --sponsor-secret KEY --subject SUBJECT
--secret NEW-KEY`; only the sponsor's X25519 key opens it, bound to the subject.
