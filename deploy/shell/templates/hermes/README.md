# Hermes role templates

`summon ROOM as ROLE [--budget N]` reads `hermes/ROLE/` and nothing else
(`native/resource-client/src/hermes.rs` compiles these files in: the files are
the roles). The roles differ only in their grants and their program text
(PLACE §2.7).

| file | read by | what it is |
|---|---|---|
| `ROLE/grants.json` | `summon`, `dismiss` | `mini-hermes-role-grants-v2`: `room` = Hermes's verbs under the room (the roster grant `chat invite` makes), `docs` = documents the role writes (name, verbs, and the law `summon` gives them: born `--in ROOM` when absent, installed by their owner when present), `program` = the program document's name and law |
| `ROLE/program.md` | `summon` | the program, written once into the room as a document (`ROOM-hermes-ROLE`); members read it, the founder edits it, Hermes reads it on every attach |
| `ROLE/budget.json` | `summon` | `fund` = the budget when `--budget` is omitted |

Placeholders are `{UPPER}` words, filled textually: `{ROOM}`, `{FOUNDER}` (the
summoner, who must be the room's founder), `{H}` (Hermes's subject: the node's
Hermes in `HOME/hermes/node.json`, or `--hermes`), `{ACCOUNT}` (`ROOM-hermes`),
`{N}` (the digest cadence, `--every`, default 3).

## `summon ROOM as ROLE [--budget N]`, in order (each step is resumable)

1. **The till.** A room without one gets `ROOM-till`, an account the founder
   owns; its target is written to the room cell's `till` field. Hermes's turns
   pay `hermes/turn` into it.
2. **The budget account** `ROOM-hermes` (`A_P`): born owned by Hermes, funded
   N from the founder's own account at its birth (one posting; the founder's
   balance moves by N and the birth fee).
3. **The roster.** Hermes joins as a friend does (`chat invite`): a grant of
   the role's `room` verbs under the room, Hermes's stream born `--in ROOM`
   under Hermes's author law (only Hermes writes it), the roster row.
4. **The documents** in `docs`, each given its law and delegated to Hermes with
   its verbs. For the librarian: `ROOM-index` and `ROOM-digest`, append-only,
   written only by the founder and Hermes.
5. **The program document** `ROOM-hermes-ROLE`, one append of `program.md`
   filled in.
6. **The room cell's fields** `hermes` = H and `hermes/account` = A_P (above the
   roster: `credit::ROOM_FIELDS_START`), so `ask` finds Hermes from a signed read.
7. **The hand-off** in `HOME/outbox/H/`: the account handoff, the invitation,
   each delegated reference, and `summon-ROOM.json` (the manifest Hermes's
   controller reads). Delivering the outbox to Hermes's inbox is the
   deployment's (as for the concierge).

`ask ROOM TEXT` is `say --to H` in the room. `dismiss ROOM` revokes the room
grant and each `docs` delegation (the founder's own revocations), sets the
room's `hermes` fields to 0, and leaves `dismiss-ROOM.json`: the budget account
is Hermes's, so the remainder (less the fleet fee) comes back as a transfer
Hermes's controller signs on its next attach. Hermes's stream and history stay.

## Roles

| role | under the room | writes | program |
|---|---|---|---|
| librarian | observe, append (its own stream: the author law refuses any other) | `ROOM-index`, `ROOM-digest` (observe, mutate) | link every document from the index; digest every N entries; answer `since` questions from the signed history |
| runner | observe, append | the outputs its program names (observe, mutate); inputs observe | `summon ROOM as runner --program @FILE`; FILE is `runner/program.md` with its Inputs, Outputs and Task lines filled in |
| gm | — | — | marked for MUD-GM: `summon … as gm` refuses here; the story verbs own the cells it would write |

## Budget

Every Hermes write is a turn: before it, the controller pays `hermes/turn`
from `ROOM-hermes` to the till in one fleet turn (`mini credit --action turn`),
so a turn costs `hermes/turn` plus the fleet fee (`tariff.base`). A turn the
account cannot cover is refused by the Host at the fleet plan (`bookRefused`),
the write is not attempted, and Hermes says "out of budget" in its stream (that
notice is the one unmetered write). `topup ROOM N` refills `ROOM-hermes`.

What binds this, said plainly: the kernel guarantees Hermes cannot spend more
than `ROOM-hermes` holds and cannot write what it holds no grant on. That each
write is preceded by its payment is the controller's discipline (its journal
shows every payment and every write); joining the posting and the write in one
transaction is K-BOOK-SLOTS (PLACE §4.8).
