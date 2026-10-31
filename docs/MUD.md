# MUD: a multi-user dungeon on the kernel

This is the present-state description of the MUD design: what is in `main`, and what is still
design. The Lean modules and the templates under `native/resource-client/templates/mud/` are the
authority. Section numbers are kept from the design of 2026-10-01 so that the `MUD §N` citations
in `Assurance/`, `Compiler/PredCompileSlotWitness.lean`, `Kernel/SealedMarket.lean`,
`native/resource-client/src/market.rs`, `journey.d/` and `templates/mud/` resolve here. Sections the
code does not cite are left out.

Each section is marked **shipped** (in `main`, with the module named), **changed** (shipped, but not
as first designed: the difference is stated) or **design** (not built).

## 0. Summary

A MUD here is a tree of cells under one realm: a sheet per player or mob, a cell per room, per
unique item, per quest and per organisation, and realm wells (accounts) for fungible goods. The
rules are cell laws written in the shell's law grammar; a referee runner computes outcomes, and the
laws bound what it may write. What is in `main`:

- the kernel pieces the laws need: slot-to-slot atoms with an offset (`leSlotsOff`), the
  deployment clock projected as `clock/now`, joint targets projected by position as
  `joint/index/{i}/…`, and realm wells (§5);
- the laws as data (`templates/mud/{sheet,room,item,quest,org,market}/law.*`, rendered to JSON
  by `templates/mud/render.py`) and the Tidewrack realm (`templates/mud/tidewrack/`);
- theorems about the sheet law and the item law as written (`Assurance/SheetLaw.lean`,
  `Assurance/ItemLaw.lean`, §5 item 6);
- a sealed-bid market, which is a separate, shipped design (§2.8).

What is not: no shell verb loads a MUD template (`shell_grammar.rs` has no `area`, `strike`, `give`
or `org` leaf; `go`, `look` and `take` are the story verbs, over a different cell). There is no
referee runner. The programs under `templates/mud/programs/` are Hoon-like text that has not been
through a compiler (`programs/README.md`). The only place a MUD template meets a Host is
`journey.d/jclock.sh`, which births one sheet and drives its clock clauses
(`templates/mud/README.md` states the evidence scope).

**What is trusted.** The referee subject. Laws bound its writes (§2.3: damage per turn, the
attacker's balance, death only at hp ≤ 0), but its choice among lawful writes is accountable, not
judged: the `witnessed` clause that would make the resolver's run part of admission
(`sheet/law.sheet-witnessed`) cannot be installed today: no host discharges `witnessed`, so the
compiler refuses any law containing it (`Compiler.supported_no_witnessed`).

## 2. The constructs

### 2.0 The realm tree. **Design**, one piece shipped.

The designed tree is a realm room `W` with areas (rooms), players (sheet, stream, account), items,
mobs, quests, organisations, markets and programs under it. Presence is on the sheet (`at`), not on
the room, so "who is here" is a read of `at` over the area's sheets.

Shipped: `room new NAME --law realm --referee SUBJECT` (`native/resource-client/src/shell.rs`,
`room_law`) gives a room whose law admits a placement (birth into the room) only by the founder and
the named referees. Nothing births the rest of the tree.

### 2.1 Rooms and movement. **Changed** (laws shipped as data; no verb).

`room/law.room`: only the area's builder writes a room; `id`, `area` and `leased` are pinned. Exits
are fields of the room (`room/fields.json`).

Movement is the owner's write of `at` on their own sheet (`sheet/law.sheet` clauses 14–18), judged
against the rooms as joint targets by position: 0 the sheet, 1 the current room, 2 the destination,
3 and 4 a key or a light item. Clause 16 requires some exit of room 1 to be room 2, clause 17 that
every locked exit taken has its key held by the mover, clause 18 that a dark room needs a lit
lantern held by the mover.

Changed from the design: joint indices are 0-based in the command's target order, with the sheet
itself at 0 (the design numbered the rooms 1 and 2 without the sheet). `go DIR` with no exit in
that direction produces no write, so the shell, not the law, would refuse it.

`templates/mud/validate.py` is a reference copy of the area-loading rules (dangling exit,
unreachable room, unplaced key, and the rest it lists). It is not the shell; no `area load` verb
exists.

### 2.2 Inventory. **Shipped** for wells and the item law; **design** for the verbs.

Fungible goods are Book assets issued by realm wells (§5, K-WELL); conservation is the Book's
(`RealmWellReceiver.realm_conservation`, `realm_holders_eq_neg_well`).

A unique item is a cell (`item/law.item`; fields `item/fields.json`: id 0, kind 1, owner 2,
where 3, worn 4, charges 5). Clause 1: only the current owner or the referee writes. Clause 4: a
referee that is not the holder leaves `owner`, `where` and `worn` unchanged. Charges only fall.
Drop and take (clauses 6, 7) read the dropper's or taker's sheet at joint index 1.

Changed from the design: the law has no `writeOnce`. What refuses the second of two concurrent
gives is the durable stale-read guard, not the law (`ItemLaw.concurrent_gives_both_law_admitted`,
`second_give_refused_after_first`). `no_dupe_unique` is therefore stated over an accepted log, in
which each step starts from the previous post-state.

### 2.3 Combat and death. **Changed** (law shipped as data, with theorems; no runner).

The sheet (`sheet/law.sheet`, 33 clauses after management; fields `sheet/fields.json`) carries hp,
mana, balance and equilibrium timestamps (`bal`, `eq`), afflictions and defences, `alive`,
`deaths`, `respawn`, `at`, and the owner's pending intent.

Changed from the design: an intent is three fields the owner writes on their own sheet in one turn
(`intent`, `target`, `skill`), not a stream entry. The referee's resolution is one joint write:
joint 0 the attacker's sheet, joint 1 the defender's. The defender's law requires a live attacker in
the same room whose pending intent names this sheet (clause 26), that the attacker had balance and
paid it (clause 27), damage per turn at most `MAXHIT` (clause 22), `deaths` monotone and moving by
exactly 1 on the 1 → 0 edge of `alive` (clauses 4, 5), and death exactly at the hp crossing
(clauses 6 and 33). The ward-blocks-paralysis pair is clause 31. Tidewrack's constants are in
`tidewrack/realm.json` (`MAXHIT` 6, `COST` 3, `ECOST` 4).

Changed from the design: every timer is written in positive form, `leSlotsOff clock/now X −K`
(that is, `now ≤ X − K`). The design wrote the balance bound as `not (leSlotsOff bal now (COST−1))`;
under `not`, an absent `clock/now` slot made the clause pass, so a step with no clock admitted any
raise. In positive form an absent clock refuses (`SheetLaw.death_needs_clock`,
`bal_raise_needs_clock`). `Compiler/PredCompileSlotWitness.lean` lowers both spellings at
`COST = 3`; they agree when the clock slot is present.

Death is admitted, never refused: there is no hp floor. Only the referee revives (clause 23), after
a prayer and the respawn time, so revival needs the clock. Two refinements of the design are design
still: `law.sheet-cure-lawful` (an affliction falls only in the turn that burns its cure; it needs
K-BOOK-SLOTS, not built), and `law.sheet-witnessed` (level 3: the referee's write carries the
resolver's run; it needs the `witnessed` oracle). Today a cure is the referee lowering an
affliction after a separate well burn, and nothing in the sheet law binds the two.

### 2.5 Mobs, quests and the referee. **Design**; the quest law is shipped as data.

A mob is a sheet under the same law, whose subject is the mob's own key held by the referee
process, so its moves are owner turns (`programs/rat.hoon`). The referee runner, the resolver and
the mob program are not built (`programs/README.md`).

`quest/cellar-key/law.quest`: one cell per player, states 0 not taken, 1 accepted, 2 done (the rat
died after acceptance, read at joint index 1), and a separate write-once `rewarded`. The reward is a
separate well mint the referee makes after `rewarded` rose: accountable, not lawful.
`law.quest-lawful` (the mint and the `rewarded` write in one turn) needs K-BOOK-SLOTS, not built.

### 2.7 Organisations. **Design**; laws shipped as data.

`org/law.org`: the founder or the sitting leader writes the org cell; a leadership handover reads
the closed ballot at joint index 1. `org/law.ballot`: eight seats bound to members when the ballot
opens, one vote each, scoped by the law's clause 4 (changed from the design, which scoped each vote
by a field-narrowed capability). The treasury is a Book account no law can see today;
`org/law.treasury` is the clause to append when K-BOOK-SLOTS (not built) projects a command's Book
leg, and until then the treasurer's office is only a delegation of `transfer`. The tally is a
program (`programs/tally.hoon`, plurality, lowest candidate number wins a tie); which voting regime
an org uses is the program it names, not a kernel object.

### 2.8 Economy and markets. **Changed.**

Gold and goods are well assets (§2.2), separate from the deployment's `credit` asset.

The order-book market of the design (`market/law.market`: four order slots, written only by the
market runner; `programs/market.hoon`) is data and text only. Its escrow is in the market's Book
account, which the law cannot read until K-BOOK-SLOTS (not built), so a runner paying out what it
never received is accountable, not refused.

What shipped instead is a **sealed-bid market** (`Kernel/SealedMarket.lean`, the law's source;
`native/resource-client/src/market.rs`; verbs `market open`, `bid`, `reveal`, `market settle`;
journey `journey.d/jmarket.sh`). One cell is one market: a founder sells `supply` units at one
uniform price to at most four sealed bids, each a commitment to (price, qty) under a blinder. The
theorems are listed in the module header (`sealed_moves_no_opening`, `market_reveal_binds`,
`fill_only_settling_within_qty`, `settles_once_by_founder_after_reveals`, `no_install_no_revoke`).
The allocation is the founder's runner, accountable, not judged. Bid deposits are refused by name
(`depositUnavailable`) because the held-account receiver is not built.

### 2.9 Player-built content. **Design**; two clauses shipped as data.

A manse is a leased room. `room/law.room` pins whether a room is leased; `sheet/law.sheet`
clause 19 admits entry to a leased room only while `now ≤ until`. The design's "Decided" step, the
concierge mirroring the lease's expiry into the room's `until` field on each renewal, is not built:
`native/grain-runtime/src/concierge.rs` has no lease code. The build verbs are not built.

## 5. The kernel items

| item | what | status |
|---|---|---|
| 1 K-JOINT-INDEX | joint targets projected a second time as `joint/index/{i}/…`, 0-based in the command's target order | **shipped**: `Kernel/DeclaredResourceController.lean`, `joint_index_of_target` |
| 2 K-PRED-OFFSET | `leSlotsOff a b k`, `new[a] ≤ new[b] + k` | **shipped**: `Pred/Core.lean`, `Compiler/PredCompile.lean` (`eval_leSlotsOff_source`) |
| 3 K-CLOCK | a law reads the time | **changed**: one clock per deployment (`Kernel/ClockCell.lean`), in unix seconds and chain slots, advanced only by an authorised ticker (`Kernel/ClockTickReceiver.lean`, `clock_monotone`) or a payment observation (`Kernel/ClockLaw.lean`); every resource law sees `clock/now`, `clock/day`, `clock/slot` (`DeclaredResourceController.now_slot_exact`). The design had the referee tick a realm clock. Journey: `journey.d/jclock.sh` |
| 4 K-WELL | realm wells: mint and burn under the well's law | **shipped**: `Kernel/RealmWellReceiver.lean` (`well_mint_requires_grant_and_law`, `well_burn_within_floor`, `credit_well_untouched`), client `native/resource-client/src/well.rs` (`mini well`), journey `journey.d/jwell.sh` |
| 6 SheetLaw, ItemLaw | theorems about the laws as written | **shipped**, as `Assurance/SheetLaw.lean` and `Assurance/ItemLaw.lean` (the design placed them in `Theory/`): `stranger_write_bounded`, `deaths_monotone_over_history`, `owner_alive_monotone_over_history`, `death_is_reachable`, `smite_refused`, `death_needs_hp`, `death_needs_clock`; `no_dupe_unique`, `kernel_holder_or_referee`. Each comes with its poles. §2 of each module is the template's JSON written out as a `Pred` term |

The design's other items (area loading, inventory, referee, combat, mobs and quests, orgs,
building, rate limiting, the GM, deployment, portals, witnessed programs, the lawful joins that
need K-BOOK-SLOTS, and a two-signature swap) are design.
