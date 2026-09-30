# MUD templates

These are the files the MUD verbs load without changing them (MUD.md §5 item 5). Everything here is a
file. Nothing here was built, installed or run against a Host. `sim.py` and `validate.py` are copies of
the rules, not the kernel.

Each item below is marked **READ** (seen at source, with file:line), **MEASURED** (from a run's artifact) or
**ASSUMED** (my choice, or something unchecked).

## Which verb reads which file, and in what order

| verb (consuming lane) | reads, in order | contract |
|---|---|---|
| `area load REALM AREA` (MUD-AREA) | `REALM/realm.json` → every `REALM/*/area.json` (the validator runs over the whole realm) → `room/fields.json` → `law.management*`, `room/law.room*` → `REALM/AREA/rooms/*.md` → `item/init.item.json`, `item/law.item*` (+ `law.item-reward*` for a quest reward) → the spawns: `sheet/init.sheet.json`, `sheet/law.sheet*` → `market/` if `shop` | `area/README.md` |
| sheet birth on first `room enter` (MUD-INVENTORY, concierge) | `sheet/sheet.json` → `sheet/fields.json` → `sheet/init.sheet.json` → `law.management*` + `sheet/law.sheet*` → `REALM/realm.json` `starterKit`, `constants`, `shrine` (= `{HOME}`) | `sheet/sheet.json` `birth` |
| well birth (`well` / K-WELL) | `REALM/realm.json` `wells` (gold, kelp, faeleaf, xp, essence) | one realm well per asset (MUD §2.2) |
| `summon REALM as referee --program …` (MUD-REFEREE) | `affliction-table.json` (compiled into) `programs/resolver.hoon`, `programs/rat.hoon`, `REALM/realm.json` `constants` | `programs/README.md` |
| `strike/cast/defend/flee/cure/pray/status/diag` (MUD-COMBAT) | `sheet/fields.json` (`intentCodes`, `skillCodes`), `affliction-table.json` (`actions`, `skills`, `afflictions`) | "The moves, as writes" below |
| `give/drop/take/wear/examine/inv` (MUD-INVENTORY) | `item/item.json` `verbs`, `item/fields.json` | `item/item.json` |
| `quests`, `quest rat-catcher [accept]` (MUD-MOBS-QUESTS) | `quest/cellar-key/quest.json` → `init.quest.json` → `law.management*` + `law.quest*` | `quest/cellar-key/quest.json` `steps` |
| `org new/found`, `office give`, `ballot open/close`, `vote`, `treasury pay` (MUD-ORG) | `org/org.json` `verbs` → `org/fields.json` → `org/charter.md` → `law.management*`, `org/law.org*`, `org/law.ballot*` → `org/offices.json` | `org/org.json` |
| `manse buy/renew` (MUD-BUILD) | `tidewrack/manses/area.json` (the plots are `leased: 1` rooms built by `{CONCIERGE}`), `tariff.json` `manseLease` | `area/README.md` (`until` is mirrored by the concierge) |
| `buy/sell/orders/cancel` (MUD-INVENTORY) | `market/market.json` → `market/fields.json` → `law.management*` + `market/law.market*` → `programs/market.hoon` | `market/market.json` |
| `tariff`, `stamina`, the daily comp (MUD-RATE) | `tariff.json` | `tariff.json` |

**Composition.** A cell's installed law is `law.management ; law.KIND [; appended files]`. In JSON that is
`{"type":"all","predicates":[<management>, ...<law.KIND>.predicates, ...]}`. This is the same rule as
`../story/README.md`. The clause numbers in every grammar file's `-- N name` comments are the indices in that
composed law. Management is clause 0. **Do not re-sort**, because the order is the order refusals are
reported in. Appended files (`law.sheet-witnessed`, `law.sheet-cure-lawful`, `law.item-reward`,
`law.quest-lawful`, `law.treasury`) continue the numbering.

**Placeholders.** `{UPPER}` words are substituted textually, as `story/` does. After substitution every
value is a canonical decimal string (`Host/Json.lean:139-145`, READ via p-templates). The realm-level
numbers are in `tidewrack/realm.json` `constants`, together with their derivation. `sim.py` refuses to
evaluate a law that still has an unbound placeholder.

## Field-number maps (fields are `Nat`, READ `Kernel/DeclaredResourceProjection.lean:18-22`; p-templates finding 2)

| kind | fields.json | numbers |
|---|---|---|
| sheet | `sheet/fields.json` | 0 id · 1 at · 2 hp · 3 bal · 4 eq · 5 alive · 6 deaths · 7 intent · 8 target · 9 respawn · 10 aff-asthma · 11 aff-paralysis · 12 aff-clumsiness · 13 def-ward · 14 skill |
| room | `room/fields.json` | 0 id · 1 area · 2 dark · 3 leased · 4 until · 5 shop · direction k (n s e w ne nw se sw u d in out): 8+3k exit-DIR · 9+3k locked-DIR · 10+3k key-DIR |
| item | `item/fields.json` | 0 id · 1 kind · 2 owner · 3 where · 4 worn · 5 charges (kinds: key 1, lantern 2, sword 3) |
| quest | `quest/fields.json` | 0 id · 1 owner · 2 state · 3 started · 4 rewarded |
| org | `org/fields.json` | 0 id · 1 leader · 2 ballot · 3 tax-rate · 4 treasurer · 5 recruiter |
| ballot | `org/fields.json` | 0 id · 1 org · 2 office · 3 open · 4 result · 5 ncand · 16..23 vote-0..vote-7 |
| market | `market/fields.json` | 0 id · 1 seq · order k (0..3) at 16+8k: side, asset, qty, price, who, filled, open |

The brief listed `maxhit`, `xp` and `essence` as sheet fields. **They are not sheet fields.** `xp` and
`essence` are Book assets (MUD §2.4; READ `M/Theory/CanonicalResourceKernel.lean:43-44`). Mirroring them on
the sheet would make a second copy of the same number, and the two copies would drift apart. The damage bound
is on `hp/delta`, and it must be a constant, because `Pred` cannot negate a slot, so no clause could ever read
a `maxhit` field. It is `{MAXHIT_LT}` in `realm.json` (`sheet/fields.json` `notFields`).

## The moves, as writes

| verb | command targets (joint index) | writes |
|---|---|---|
| `go DIR` | 0 my sheet · 1 my room · 2 the room `exit-DIR` names · 3 its key, else my lantern · 4 my lantern if both | `at := room 2's id`, `expected` = my `at` |
| `flee DIR` | as `go` | `at`, and `intent := 4` (clause 10 needs balance; the referee charges it) |
| `strike S SKILL` / `cast S SPELL` / `defend` | 0 my sheet | `intent := 1\|2\|3`, `target := S`, `skill := code` (one owner turn; the fee pays for it) |
| (referee resolves) | 0 attacker sheet · 1 defender sheet | `resolver.hoon`'s writes, one command |
| `cure AFF` | a Book send: `--to REF --asset HERB --amount 1 --topic cure/AFF` | then the referee burns the herb (K-WELL) and writes `aff-AFF := 0` |
| `pray` (dead) | 0 my sheet | `intent := 9`; the referee revives after `now >= respawn`: `alive 1, hp HPMAX, at HOME, intent 0` |
| `give S ITEM` | 0 the item | `owner := S`, `expected` = me (the stale-read guard is what refuses the second of two concurrent gives) |
| `drop ITEM` / `take ITEM` | 0 the item · 1 my sheet | `owner := REF, where := my at` / the referee writes `owner := me, where := 0` |

**`go e` with no east exit.** MUD J-MUD-1 expects this refused with `law-denied: exits`. The law never sees a
direction, only the new `at` and the two rooms. So a `go e` that has no `exit-e` produces **no destination and
no write**, and the shell has to refuse it itself. What the kernel refuses is a forged destination that no
exit of the current room reaches (`sim.py` J-MUD-1 r4, clause 16 **exits**). To make the literal row a kernel
refusal, the move would have to carry its direction as a field. I judged that not worth a field. It is flagged
in the lane report.

## The clauses that need atoms that have not landed

Today's `Pred` has `eq le memberOf writeOnce monotone witnessed not all any` (READ `Pred/Core.lean:103-122`
via p-templates). `eqSlots`/`leSlots` landed on branch `k-sloteq` 342d57d (READ `planning/place/k-sloteq.md`),
and their JSON is `{"type","left","right"}`.

| atom / slot | lane | clauses that need it |
|---|---|---|
| `leSlotsOff A B k` = `new[A] ≤ new[B] + k`, JSON `{"type":"leSlotsOff","left","right","offset"}` (**key names ASSUMED**) | K-PRED-OFFSET | law.sheet 25 death-timer, 27 attacker-paid, 28 bal-paid, 29 eq-paid |
| `clock/now` | K-CLOCK | law.sheet 10 bal, 11 eq, 19 lease, 23 revive, 25, 27, 28, 29 |
| `joint/index/{i}/resource/field/{n}/{view}` (i = the command's 0-based target order; the id-keyed original is `joint/target/{target}/…`, READ `c-c2:Kernel/DeclaredResourceController.lean:176-180`) | K-JOINT-INDEX | law.sheet 14–19 (movement), 26–27 (combat); law.item 6 drop-here, 7 take-here; law.item-reward 8; law.quest 5 table; law.org 3 leader-by-ballot |
| `joint/target/{BOOK}/balance/{A}/{ASSET}/delta` (PLACE's name, **ASSUMED**) | K-BOOK-SLOTS | law.sheet-cure-lawful 34; law.quest-lawful 9; law.treasury 7 |
| `witnessed {VK_*}` with an oracle (today `failClosed`, so it is always false) | K-RAN (NOCK.md) | law.sheet-witnessed 33 |
| `Scope.maxDelta`, `Scope.fields` | K-FIELDS | `org/offices.json` (`needs`); a delegate request carrying them is refused by the client today (READ `workspace.rs:728-734`, exactly six keys) |

**What happens before they land.** A law naming a slot that is not projected does **not** admit silently.
The atom that reads the missing slot is false, so that clause fails closed, and only when its guard lets it
be evaluated. So a sheet law installed with K-JOINT-INDEX missing refuses every move and admits every read.
`leSlotsOff` is a different case. It is a new `Pred` constructor, and the Host parser takes exact keys per
constructor (READ `Host/Json.lean:206-230` via p-templates). **`law.sheet` will not install at all** until
K-PRED-OFFSET is in the Host. The same holds for `eqSlots`/`leSlots` until the k-sloteq codec v4 is in the
deployed candidate.

## Measured limits the templates run into

- **Field count.** MEASURED: the deployed store refuses the 4th created field of a resource
  (`RejectReason.overflow`, `product/mj-journey.md` K4 row; "expected until final integrator",
  `planning/SESSION-STATE.md:53`). A sheet has 15 fields, a room up to 44, and a ballot 14. c-c2's
  projection header says "there is no page capacity" (READ `c-c2:Kernel/DeclaredResourceProjection.lean:1-6`).
  So **every MUD cell needs the C2 growth exit in the candidate**. On the old store, `area load` fails at
  the first room's 4th field.
- **Fee.** `tariff.base` 3 is MEASURED in M8 (via p-templates README item 12).

## ASSUMED (each is the consuming lane's first check)

1. The grammar extensions (`render.py` header): `--` comments, a `-- kind: K` first line, `<=`,
   `eqSlots/leSlots/leSlotsOff`, and the slot words `clock`, `joint I KIND NAME [VIEW]` and `slot PATH`.
   P-LAW's parser has to accept them, or strip the comments. MUD §2.1 uses `--` comments and `joint/index/…`
   paths in its own law text, so these extend the same idea.
2. Ids are realm-local numbers: room ids 101–308, item ids 5001+/6001+/7001+, and a sheet's id = its
   subject. They are not cell digests. The laws compare them with `eqSlots` and pin them with `eq`. A digest
   would need a width no compiled profile has.
3. A mob is its own enrolled subject, and the referee process holds its key (MUD §1 table: "a mob … subject
   + account + sheet cell + Nock program"). §2.5's "`owner ↦ REF`" is not used. If the mob were REF, the
   owner clauses would bind the referee's own combat writes on the mob.
4. The intent lives on the attacker's own sheet (`intent`, `target`, `skill`), not in a stream entry. MUD
   §2.3's defender clause reads `joint/index/3/field/author/after` of a K-STREAM entry, but PLACE §4.4's
   `StreamEntry` is `{topic, payloadDigest, to, ref}`. It has no author, and it is an `eventHistory`
   append, not declared fields (READ `planning/PLACE.md` §4.4). Putting the intent on the sheet gives the
   same binding with slots that exist, and "signed by the attacker" comes free from clause 1.
5. Joint slots of observe-only targets are visible to the primary target's law (MUD A2, not traced).
6. A subject id that nobody signs as exists for empty ballot seats (`{NOBODY}`; `sim.py` binds 0).
7. `valid_until`/`notAfter` in `org/offices.json` is a block height (09-29 decision).
8. The Hoon programs' sample: `now` in ctx, keys `'I/N'`, `@s` values (`programs/README.md`).
