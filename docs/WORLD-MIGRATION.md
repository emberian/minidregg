# World migration: carrying the demo's world across a re-genesis

A Store is pinned to its Host image, so moving the demo onto a new Host means a new genesis. The world
migration carries what the demo holds across that genesis, so that only hashes, heights and ids change.
The tool is `deploy/migrate/world-migrate`. The operator wiring lives in dregg-infra (`demo-dry-walk`
with `WALK_MIGRATE=1`, and `mini-reenroll` with a carry). This page is the present state. It is rewritten
whole when anything here changes.

## What the demo's Store holds

The inventory below was read from a copy of demo-dry's Store taken on 2026-11-07 at 02:45Z. The Store was
on candidate 976f31067e01, Host `9b9ca712…`, pinned config `510dbbf5…`, genesis 2026-11-05 21:50Z. The copy
was read through each member's own signed reads (`world-migrate capture`).

| subject | who | key | balance | what it holds |
|---|---|---|---|---|
| 7 | sponsor `ember` | `NODE/keys/sponsor.key` | 61,068,766 | the operator's purse; every provision is paid from it |
| 70 | clock | `NODE/keys/clock.key` | genesis | the clock cell's only ticker |
| 30 | pay observer | `/etc/mini/pay/observer.key` | genesis | genesis enrollment (`/etc/mini/pay/genesis-enrollments.json`) |
| 14415825148291336699 | `house` (seed account; secret shredded) | hosted | 1,072,463 | 41 references; founds lobby, feedback, tale, the seeded documents, 3 app grains |
| 13511655580297377751 | `sage` (seed guest) | hosted | 1,225,000 | the tale's GM; field-notes writer; 1 lobby post |
| 14548481775198860328 | `public` (public reader) | hosted | 1,225,000 | the published documents' reader (13 references) |
| 17439069868963619863 | `ember3` (door, paid route) | hosted | 340 | lobby member, 1 lobby post, tale player, a `research-consent` cell (field 1 = 1, CC0) |
| 15533197528133451501 | `jorendregg` (door, free route, web-only) | hosted | 1,225,000 | enrolled and funded; no workspace (never ran `init`) |
| 12570880118135778366 | `ember2` (roster friend) | hosted | 1,225,000 | enrolled and funded; no workspace |
| 11687671680779943287 | `lobby-hermes` (agent) | in `/var/lib/mini/lobby` | its purse | lobby member, the librarian resident |
| 12310133694182247163, 11385637078272555732 | `lobby-hhost`, `lobby-hprov` (agents) | in `/var/lib/mini/lobby` | | the resident's Host and provider custody |
| 14835957914534074161 | `enrollment-float` (pay rail) | `/var/lib/mini/pay/float` | | the pay route's enrolment float |

The `dw-*` sessions (door-walk probes), `uxprobe` and `ember` hold no hosted key. They carry nothing.

What the members made:

- **Rooms.** `lobby` (founder house) has 5 members: house, sage, ember3, lobby-hermes, and a subject
  `10490016690602142714` that no longer exists. That subject is jorendregg's from the 11-03 world. The door
  processor invited it from the request's stale subject, and the same subject has a `tale` player cell.
  Each member also has a `feedback` room founded by the sponsor. The lobby holds 6 entries: 4 by house,
  1 by sage and 1 by ember3 ("hello everybody"). Hermes has posted nothing.
- **Documents.** The house owns 21: welcome, what-is-mini, house-rules, field-notes, a-refusal-explains-itself,
  the-lost-reply, the-lamplighters-note, lobby-index, lobby-digest, lobby-tally, lobby-hermes-librarian,
  tale/cast, tale/chapters, tale/index, tale/table, and three app package and snapshot pairs. All of them
  come from the seed. Field-notes has one line by sage. No member other than the seed accounts owns a
  document.
- **Story.** `tale` has house as author, sage as GM, and ember3 as a player at scene 0, turn 0.
- **Cells.** ember3's `research-consent` (declared, open law, field 1 = 1).
- **Grants.** Each member's references (account, factory, lobby, lobby-me, tale, tale/me, tale/scenes,
  welcome and the like). The door processor and the seed re-hand the publications (welcome, lobby, board,
  operations, grain-snapshot).
- **App grains.** Three, all the house's: EtherCalc `a15709830973330553399`, Etherpad
  `a13082149311862657913` and reveal.js `a11025972086644045952`. Their data is in `/var/lib/mini-spk-worlds`.
- **Door.** Two enrolled requests are kept: ember3 (paid) and jorendregg (free). Their status pages are
  kept too.
- **Pay.** ember3 paid 50.000354 DREGG on mainnet (`payments/141061258…json`, memo `enrol:v2`, bound to
  Host `9b9ca712…` and config `510dbbf5…`). The claim enrolled ember3 and credited their account.

## What carries, and how

| item | carries | how |
|---|---|---|
| each hosted member's key | exactly | the same key files (`sessions/NAME/keys`); ship.sh keeps `keys/` |
| each hosted member's subject | exactly | `mini-reenroll` with the carry: a home-subject enrollment (`mini enroll --action plan --home-subject S`) on the fresh genesis |
| each hosted member's balance | exactly | the provision is funded with the old balance; after the replay the sponsor tops up what the replay's turns cost (`mini fleet --action transfer`) |
| workspaces | re-made | `world-migrate init`: `init mini.key SUBJECT` for each member who had one |
| room membership | by re-authoring | the founder's `chat invite`, then the member's `chat join`; the door processor re-invites door members first |
| messages | by re-authoring | each missing `say`, as its author, in the old world's height order (`say --in ROOM TEXT`) |
| story players | by re-authoring | the author's `story invite`, then the player's `story join` |
| declared cells a member made | by re-authoring | `create NAME declared open FIELDS`, then `invoke … create F V` and `submit` |
| documents a member owns | by re-authoring | `doc new`, then each missing line by `doc append` and `submit` (current text; line authors are checked) |
| the seed accounts' content | rebuilt | the walk's seed step (house, sage, public: `MIGRATE_SEED_ACCOUNTS`); compared, never re-authored |
| door requests and status pages | kept | ship.sh keeps every enrolled request whose account exists |
| app grains and the data inside them | exactly (the /var bytes), walked once on demo-dry for one grain (2026-11-09, below) | `world-migrate capture` STOPs and exports each grain a member owns, as its owner (`apps stop`, `apps export`: the stopped /var bound to its STOP receipt, signed by the old Store's completion custodian), into `DIR/grains/GRAIN/` with `carry.json` (owner, app, class, the old pinned `completionCustodianKey`), and puts each export's image digest in `before.json`. `world-migrate grains` (after grain-world, before the seed) places it in `/var/lib/mini-apps/carried/GRAIN/`. The owner then runs `apps install APP --carry GRAIN`: the worker admits only the owner, the same app and class, and one install per carry, and it runs `spk-host grain install --import`. Then `apps share` for each member. The seed writes nothing into a carried grain. Verify needs a grain carried from each old one, with the same owner, app, class and shares, whose imported image is the export's digest. House grains count too (a member may write into them) |

The grain row was walked on demo-dry on 2026-11-09, at overlay `33b20ce9d8c9` (hotfix/stop-fence-on-980d
7c486537c on candidate 980d80c5), for one grain: the house's reveal.js deck `a15221083032525807762`. The house
STOPped it (generation 6) and exported it. world-migrate's own `export_grains` copied the export and its
`carry.json`, and its `carry_grains` installed it with `--carry`. Two owners were tried:

- **The house, which already holds the deck.** The carry is refused as `carryRefused` ("house already holds
  a15221083032525807762") before the claim and before any install. A re-genesis never meets this case, because
  the new world holds no grains yet.
- **sage, who held no grain of it.** The deck was carried as `a12530561198587150331`. The grain record's
  `carriedImageSha256` and the broker's volume `importSha256` both equal the export image `ab959a9a39be9c0e…`.
  `diff` found no grain differences. The carried grain runs generation 2, and its public page is byte-identical
  to the source deck's (both answer 200). sage's copy was then deleted; its 5 MB volume is retained.

A second walk the same night carried the deck (generation 8, image `cbda581dc969…`) into ember3, who held no
grain of it. Its share was made again for sage: `apps share` bound sage's route, and one `apps renew` enrolled
it. sage opened the carried deck through that route: the bootstrap answered 303, and the page and `deck.md`
answered 200 with the house's slides. Without the cookie the page answered 403. The grain diff was empty, and
`release_carried` removed `carried/` and the worker's `exports/` copy while keeping the walk's own export. The
house's original was not shared, because v1 has no read-only share and no verb that drops a share. The cleanup
delete of ember3's copy is stuck: its STOP completion was marked submitted (op38), but the lookup still answers
`absent`, so g2 stays uncertain and the routes stay in place.

The house's deck was started and renewed again afterwards, and its public page answers 200. Three faults
were fixed along the way:

- a retained export answered for an older STOP;
- an instance conflict marked the package refused for every member;
- every START of a carried grain was refused, because its mount differed from the volume record its import
  created.

What cannot carry, and why:

- **Hashes, heights, world roots, receipts, event and transaction ids, and capability, account and cell
  ids.** These belong to a genesis. Verify compares through them: subjects map to names, and heights are
  dropped.
- **The agents' subjects.** lobby-hermes, lobby-hhost, lobby-hprov and enrollment-float are enrolled by their
  installers (install-hermes, mini-pay-rail) with Host-reserved subjects. Their balances are their purses,
  refilled by the walk. The home-subject enrollment would carry them, but it is not wired into those
  installers.
- **The sponsor's balance.** It restarts at the genesis parameter (`sponsor.initialBalance`, 67,395,000). It
  funds the re-enrollment of every member at their old balance, the seed, Hermes and the top-ups, so
  carrying it would count the same units twice.
- **History.** Each document carries its current text and who wrote each line. Each room carries its
  entries in order. A struck line, an edit that was later overwritten, a refused attempt and a read do not
  replay. The old world's history stays readable in the retired Store.
- **Pay claims.** The memo of a mainnet payment pins the old Host and config. The new world can neither
  claim it nor credit it again. Its effect (the enrollment, the subject, the balance) carries.
- **Grains in the worlds already retired.** Before 2026-11-09 nothing was exported, and ship.sh stopped those
  grains by unit, without a STOP through Mini. So they have no STOP receipt and cannot be exported. Their
  volumes stay on disk. The 2026-11-09 audit compared both of that night's retired worlds against a fresh
  seed and found nothing beyond the seed's own writes.
- **ember3's `factory` reference.** It is an observe grant on the factory that the pay route's birth
  context carries and the sponsor's provision does not. Nothing ember3 did needed it: the
  `research-consent` cell is re-created without it.
- **Hermes's per-world state.** Its step records, its reconciliations and any undecided prompt are
  per-world and set aside by the walk's prep step.

## The tool

`deploy/migrate/world-migrate` runs as root on the box. Every change goes through the member shell
(`mini-shell-ssh`) under the acting member's own account (`mini-s-NAME`) and key, the way `seed.sh` seeds
the house. The sponsor's lines run as the Store's account. It never touches a Store file or a Host
operation directly, so it survives changes to the Host's implementation.

```
world-migrate capture DIR   old world -> DIR/before.json + DIR/carry.json (refuses if before.json exists)
world-migrate init DIR      after mini-reenroll: init for every member who had a workspace
world-migrate replay DIR    re-author what a fresh diff says is missing, then settle balances (DIR/journal.jsonl)
world-migrate verify DIR    DIR/after.json and DIR/verify.txt; exit 0 iff nothing carried was lost or changed
world-migrate diff A B      the same comparison between two captures
```

- **Re-runnable.** Every replay pass starts from a fresh capture and diff, so it re-authors only what is
  still missing. The journal records each action. A refusal the Host reports as `tail-bound` runs
  `mini-certify` once and retries.
- **Safe on failure.** A capture refuses to overwrite `before.json`. A replay refuses while the serving
  Store's pinned config is still the captured one. `mini-reenroll` takes a carry only into the genesis that
  followed the captured world (the newest retired Store's pinned config must be the carry's), so a stale
  carry never funds a later genesis.
- **Verify** prints four sections:
  - carried items that were lost or changed (these must be empty);
  - additions made by the new world;
  - the seed accounts' content (informational, since the seed rebuilds it);
  - ids.

  Keys and balances count for every member.

The rehearsal frame is `deploy/migrate/rehearse-hbox.sh`. It runs a copy of the demo's state on hbox in a
private mount namespace at the box's own paths. It has the box's accounts: mini-core owns the Store, each
member runs as mini-s-NAME in mini-sessions, and each member has a delegated consent worker. It runs the
box's scripts with one override (as_mini switches with setpriv instead of systemd-run).
`rehearse-hbox.sh migrate INCOMING RUN [SEED_SRC]` runs the whole migration in the demo run's order.
`rehearse-regenesis.sh --undo TS` returns the frame to the retired world, so the rehearsal can run again.
The frame has no app market, no Hermes and no pay rail: those steps are the walk's.

## Rehearsal (hbox, 2026-11-07)

The rehearsal used a copy of demo-dry's state (1.5 GB under `/ci/migrate`, mode 0700): the Store
(SQLite online backup), `/etc/mini` without `credentials.key` or `pay/rpc.env`, the session homes with the
hosted keys, and the door, lobby, pay and apps trees. The target was candidate f2dae81d3680 from main,
whose objective pin is the same as the demo's.

The rehearsal ran four times, with `rehearse-regenesis.sh --undo` between runs. Run r4 started from the
untouched copy and ran `rehearse-hbox.sh migrate … r4`, seeded with the walk's seed overlay
(`~/.local/state/demo-dry-walk/seed-overlay`, as the walk applies it). The steps were:

1. capture, 4 s;
2. the regenesis onto f2dae81d3680;
3. `mini-reenroll --all` with the carry;
4. `world-migrate init`;
5. the seed, 30 s in the frame (no apps);
6. one door pass;
7. replay, 42 s;
8. verify, 4 s.

Results:

- Every hosted member got the same subject and the same key: house, sage, public, ember3, ember2,
  jorendregg.
- Every balance matched the old world. ember3 was 340 before and 340 after: the provision funded 340, the
  replay's turns cost 7 and the sponsor topped up 7. House was 1,072,463 before and after: the seed cost
  152,350 and the sponsor topped up the same.
- The door pass put ember3 back into the lobby and the tale. The replay re-imported ember3's `factory`
  grant from the birth context, posted "hello everybody" as ember3 and re-made `research-consent` with
  field 1 = 1.
- Verify (`DIR/verify.txt`):

  ```
  ## carried: the members' own, lost or changed (must not differ): 0 difference(s)
  ## added by the new world (nothing of the old is missing; informational): 3 difference(s)
     ember3 gains the per-member feedback room mini-reenroll founds for every member (refs feedback, feedback-me)
  ## seed accounts' content (house public sage: rebuilt by the walk's seed step, informational): 37 difference(s)
     the house's three app grains and their package/snapshot refs, Hermes's lobby membership and its
     lobby-index/lobby-digest/lobby-hermes-librarian/lobby-till, and public's reader refs: the frame has no
     app market, no Hermes and no pay rail, so the walk's apps-bootstrap/grain-world/hermes steps rebuild
     these on the box; the old welcome's duplicated transclusion line (the old seed ran twice)
  ## ids (allowed): 0 difference(s)
  ```

- The rollback was rehearsed too. `mini-regenesis-undo TS 976f31067e01` ran on r4's world, the old
  candidate's Store was started on the restored state, and a fresh capture showed 0 differences in every
  section against the capture taken before the genesis.

Two reds that the rehearsal found are fixed in the code:

- On candidate f2dae81d3680, `mini-reenroll`'s possession signature refused "the resident consent provider
  ended" for every friend. Local consent in the member's account cannot read the Store's checkpoint MAC
  key, which the consent provider opens since the Host's light opening. `mini-reenroll` now signs through
  the member's delegated consent socket.
- The sponsor's transfer of 152,336 to the house was refused `capability-rejected`. The sponsor's spend
  grant bounds a turn's cost: 100,000 was refused and 52,336 admitted. Settling now moves at most 50,000
  a turn.

The frame did not exercise five things:

- the app market;
- Hermes;
- the pay rail and its watcher (whether the new world's watcher meets ember3's old memo was not seen);
- the unit restarts;
- ship.sh's notice and its app-market and controller retirement. The rollback reverses those, but the
  frame has none to reverse.

The copy was removed from hbox with the accounts and mountpoints it used (`rehearse-hbox.sh clean`).

## The demo run

This is the operator's run, on ember's word. It runs from the Mac, with both repositories on main:
minidregg with `deploy/migrate`, and dregg-infra with the walk steps, `mini-reenroll` and
`mini-regenesis-undo`. `CP` is a candidate from main whose gate passed; a non-rehearsal ship needs
`gate/jdeploy3-result.json` PASS. Copy it out of the builder's rotation first, for example to
`/home/hbox/lanes/infra/cand-<id>`.

```
# 0. before the window, nothing on the box changes: the objective pin and the Hermes worker root for CP
cd ~/dev/dregg-infra && git pull --ff-only && (cd ~/dev/minidregg && git pull --ff-only)
edge/demo/preship-check "$CP" && edge/demo/preship-check --hroot "$CP"     # wait for hroot-<id>/pins.json on hbox

# 1. the frame: this checkout's infra on demo-dry (the walk's frame step without its baseline restore)
OUT=$(mktemp -d); cp edge/demo/friends/*.pub "$OUT/"; echo demo-dry > "$OUT/BOX"
rsync -rlt --delete --chmod=D755,F644 --exclude='.*' --exclude='/friends/' edge/demo/ demo-dry:/usr/local/lib/demo/infra/
scp -q edge/demo/install-demo.sh demo-dry:/root/install-demo.sh
BOX=demo-dry MINI_ROSTER_DIR="$OUT" bash edge/mini/install.sh
ssh demo-dry 'DEMO_REMOTE_TENANTS=nd-testground DEMO_CONTAINER=1 DEMO_HOSTNAME=demo-dry DEMO_DOMAIN=demo.dregg.online bash /root/install-demo.sh --on-box --after-mini'

# 2. the migration walk: capture, genesis, members, reenroll, migrate-init, pay, grains, Hermes, seed, door, migrate
WALK_MIGRATE=1 MIGRATE_SRC=~/dev/minidregg WALK_RESTORE=0 WALK_SAVE=0 \
WALK_STEPS="disk preship-check hroot stream capture prep ship members apps-bootstrap reenroll migrate-init pay grain-world hermes seed door migrate public seen" \
  edge/demo/demo-dry-walk "$CP"
```

Notes on these commands:

- `WALK_STEPS` leaves out `frame`. With `frame` in it, a fresh walk would restore the pristine container
  baseline and drop the world. With `WALK_STEPS` set, the walk never restores a snapshot.
- The seed overlay at `~/.local/state/demo-dry-walk/seed-overlay` is applied by default. It is what seeded
  the current house content. Keep it, or the house's documents and lobby posts change to main's seed text
  (verify reports this in its seed section).
- The walk's `walk.tsv` carries the rows `migrate.capture`, `migrate.init`, `migrate.replay` and
  `migrate.verify`. `demo-dry:/var/lib/mini/migrate/done-<walk id>/verify.txt` is the diff. It is
  `/var/lib/mini/migrate/<walk id>/` while verify is still red.
- A red replay or verify leaves the new world serving and the run directory in place.
  `ssh demo-dry /root/walk-<id>/box.sh exec migrate` re-runs the step. It is resumable and re-authors only
  what is still missing.

**Downtime.** These estimates come from the last genesis walk on demo-dry (2026-11-05) plus the rehearsal:

| step | time |
|---|---|
| capture | about 10 s |
| prep and ship (the Store restarts on the new genesis) | about 45 s |
| members, apps-bootstrap and reenroll | about 50 s |
| hermes | about 30 s, when the worker root was built in step 0 |
| seed | about 28 min, almost all of it the three app installs |
| door, then migrate | about 2 to 3 min |

The site stops answering for about a minute around the ship. It then serves a new world that is
incomplete for about 30 minutes. Members' own content is back about 33 minutes after the capture. Anything
a member does between the capture and the ship is lost, a window of about 1 minute. Anything done between
the ship and the migrate step happens in the new world, before their old content returns. To keep the
window empty, stop the door (`ssh demo-dry systemctl stop mini-door.service mini-door-process.timer`)
until the walk ends.

**Rollback.** Nothing is deleted. ship.sh moves the old Store to `/var/lib/mini/store/retired-<TS>`, frozen
and read-only, and the walk's prep sets the old Hermes, lobby and apps.json state aside in `/root/walk-<id>/`.
To go back, at any point after the ship:

```
ssh demo-dry '/usr/local/lib/mini/mini-regenesis-undo <TS> 976f31067e01 /root/walk-<id> && /usr/local/lib/mini/infra/ship.sh --on-box 976f31067e01'
```

- `<TS>` is the stamp in ship.log's "REGENESIS — old Store moved to …retired-<TS>".
- `976f31067e01` is the candidate the old world runs today. It is still under `/var/lib/mini/candidate/`.
- The new world is moved aside as `abandoned-<TS>-<now>`, next to each thing it replaced.
- The plain ship of the old candidate restarts every unit on the restored world.
- The rollback was rehearsed for its file moves and for the restored world: 0 differences. Its unit stops
  and the plain ship were not rehearsed; they are the box's ordinary paths.
