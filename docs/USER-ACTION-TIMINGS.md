# User action timings (batch 4, b9450147f; coverage map covers b4 to b6)

Present-state table, rewritten whole. Candidate `b9450147f571b6e3f9dffd6ed649024137ad8a0a` on hbox, a fresh scratch
world (demo params, Objective policy, funding 1,225,000, five members), driven by `~/xp/tm.sh` (wall table),
`~/xp/bd.py` (CPU by process role) and `~/xp/st.sh` (strace) on hbox. The bar is ember's: on a modern nvme
machine nothing takes substantially over about 1 ms of warm server-side work.

**Read this first.** hbox ran at load average 13 to 15 for the whole measurement (about 100 other sessions),
and `/` is an ext4 NVMe at 93% full. Every wall number is inflated by contention, and an fsync cost about 12 ms
here. The CPU split and the syscall counts are not load dependent; trust those, and the ratio fresh vs aged.
Nothing here is a quiet-box number. Hermes asks, typed tools, apps install/start/first page and the door
enrol are NOT measured: the scratch world has no Hermes resident, no door, and apps installs are still red
(Simple Todos stops at `routing` no-grant; Etherpad's download is refused upstream).

## What the bar says

Warm wall time for an ssh-carried verb has a floor of about 7 ms (client `help` with no Host call, ssh
excluded) and is 100 to 3,000 ms for everything that reaches the Host. No Host-reaching action is near 1 ms.
The CPU the world spent per action, summed over client, relay, consent, codec and Store processes
(`bd.py`, median of 5 warm runs, aged world at height about 620), is 35 to 935 ms; the rest of the wall is
waiting (fsync and IPC).

## Wall time per action

Cold = first call by a fresh member or name; warm = median of three further calls. ms. "fresh" = height
54 to 143, "aged" = height 531 to 620 (after 480 writes). `-` = not applicable, `x` = broken driver row
(see notes).

| action | fresh cold | fresh warm | aged cold | aged warm | grows with history |
|---|---|---|---|---|---|
| first signed read (new member) | 543 | - | 629 | - | no (but see "idle member" below) |
| signed read `credit`, member with 128 refs | 13,129 | 650 | 7,265 | 6,933 | **yes: 10x** |
| chat say | 935 | 1,103 | 1,399 | 1,674 | modest |
| tail -n 5 | 2,660 | 2,065 | 2,638 | 2,603 | modest |
| doc new | 2,584 | 2,850 | 3,733 | 4,016 | yes |
| doc append (propose) | 857 | 1,155 | 1,039 | 993 | no |
| doc submit | 866 | 1,063 | 926 | 1,073 | no |
| doc show | 664 | 515 | 698 | 449 | no |
| chat new | 8,257 | 7,665 | 14,474 | 11,820 | **yes** |
| chat invite + join | 17,807 | 21,039 | 19,400 | 21,337 | flat but huge |
| create object | 2,930 | 2,779 | 2,096 | 2,956 | no |
| delegate (propose / submit / publish) | 791 / 1,592 / 355 | 919 / 1,829 / 272 | 1,457 / 1,723 / 463 | 1,311 / 2,199 / 450 | no |
| import (recipient) | 676 | 415 | 435 | 416 | no |
| revoke (propose / submit) | x | x | x | x | driver row broken |
| pay status account | 969 | 1,178 | 1,138 | 707 | no |
| bend publish | 919 | - | 6,361 | - | **yes** |
| bend create object | 2,685 | 2,954 | 2,888 | 3,753 | no |
| bend run | 1,369 | 1,762 | 7,278 | 10,229 | **yes: 6x** |
| bend answer / await / deliver | x (driver bug) | x | x | x | see batch-3 numbers below |
| bend settle | 266 | - | 5,846 | - | **yes: 22x** |
| story new (tale) | 28,273 | - | 44,881 | - | yes (and huge) |
| certify (a 256 tail) | 2,345 | - | 25,146 | - | **yes: 10x** |
| restart (wall) | 2,508 | - | 12,548 | - | **yes: 5x** |
| first read after restart | 605 | - | 18,956 | - | **yes: 31x** |

Batch 3 numbers for the rows the driver broke (same kind of box, load 6 to 10): bend answer 0.45 s, deliver
0.5 s, settle 0.5 s, await 0.2 s; revoke propose 0.3 s.

Web (measured in a separate pass on the aged world, `wt.sh`, gateway on loopback, ms, four warm GETs):
`/` 25 to 33, `/doc` 20 to 32, `/story` 17 to 28, `/room` 18 to 29, `/bend` 19 to 29, `/apps` 41 to 50,
`/receipts` 45 to 68 (first 155), `/verb` 14 to 17, `/tour` 19 to 30, `/export` 16 to 27, anonymous public
`GET /` 26 (first 77). Form POSTs: **`POST /doc/new` 6.5 to 7.7 s** (the same write path as `doc new`, plus
the web's own spawn). The web read pages are 15 to 70 ms, well above 1 ms but three orders below the Host-reaching
actions; the 40+ ms of `/apps` and `/receipts` is server-side rendering of workspace files.
(The first wall table's web rows, 5 to 70 ms, ran against a helper that could not start the member shells and
are discarded.)

## Where the milliseconds go (warm, aged world, `bd.py`, median of 5, direct client without ssh)

CPU ms by role per action; `wait` = wall minus all CPU, i.e. time blocked on fsync/IPC.

| action | wall | client | store | consent | codec | relay | other | wait |
|---|---|---|---|---|---|---|---|---|
| `help` (pure client floor) | 7 | 6 | 0 | 1 | 1 | 0 | 16 | 0 |
| whoami | 7 | 7 | 0 | 1 | 1 | 0 | 26 | 0 |
| doc show | 364 | 18 | 4 | 6 | 7 | 1 | 17 | 312 |
| read feedback | 399 | 22 | 6 | 10 | 10 | 2 | 38 | 311 |
| doc append (propose) | 912 | 40 | 11 | 20 | 21 | 4 | 34 | 783 |
| say | 3,372 | 30 | 26 | 53 | 52 | 9 | 42 | 3,160 |
| doc submit | 3,047 | 20 | 25 | 59 | 62 | 8 | 42 | 2,831 |
| tail -n 5 | 2,180 | 174 | 15 | 41 | 43 | 7 | 43 | 1,857 |
| credit (member with 128 refs) | 11,179 | 204 | 58 | 170 | 171 | 31 | 73 | 10,471 |
| create object | 7,827 | 39 | 32 | 163 | 160 | 24 | 77 | 7,333 |
| bend create | 7,528 | 37 | 27 | 155 | 154 | 22 | 80 | 7,052 |
| chat new | 18,537 | 109 | 102 | 345 | 343 | 51 | 94 | 17,493 |

(`other` includes the world's idle background processes, so it is a floor of noise, not work; Host CPU
shows as 0 because the Host runs under the relay and consent residents. Every Host-reaching action burns
50 to 935 ms of CPU across client, consent and codec; consent and codec residents are each as expensive as
the Store.) 90 to 99% of wall is waiting, and the next section shows what it waits on.

## What the waiting is (strace -f -T on the direct client, aged world)

| action | syscalls | fsync calls | time in fsync | other | execve |
|---|---|---|---|---|---|
| `credit` (a READ) | 19,808 | **697** | **8,822 ms of 12,060** | 5,006 openat, 1,269 ms in one recvfrom | 13 |
| `say` | 4,535 | 43 | 535 ms of 2,733 | poll 2,036 ms waiting for the Host | 13 |
| `chat new` | 17,597 | 496 | 6,389 ms of 19,597 | poll 8,556 ms, recvfrom 4,205 ms | 13 |

For `credit` the fsyncs land in the attempt directory the read retains: 122 in `attempts/a-HASH`, 100 each in
its sub-attempts `0` and `1`, 21 in `sources/`. The number is proportional to the member's reference count
(128 refs, 698 retained attempts), which is why `credit` is 650 ms for a member with few refs and 7 to 13 s
for the member that my driver filled with objects. For `chat new` the fsyncs include 24 each of every parent
directory up to the world root (`sessions/member-1`, `sessions`, `.../mini`, `.../lib`, `.../var`, `root`):
each durable file write fsyncs the whole ancestor chain. Every verb also spawns 13 processes.

**Idle member.** A member that has not touched the world for a few hundred heights pays the gap on its next
action: member-3's `credit` took 543 ms at height 202 and **61 s** after height 620, member-1's first read
after a restart at height 620 took 19 s. That is the consent catch-up measured on batch 2 as flat
(0.46 s at 803 for a never-read member), reappearing for a member whose consent record is hundreds of heights
behind. The batch-5 change that limits a lagging consent provider's catch-up should be checked against this.

## Ranking by user pain (what a person feels)

1. **First action after being away** (consent catch-up): 19 to 61 s. Owner hot-path.
2. **chat invite + join 21 s, chat new 8 to 14 s, story new 28 to 45 s** (a stranger's first room): owner
   hot-path (Host/Store) for the template submits, exorcist for the per-file directory-chain fsyncs.
3. **bend run / deliver / settle / publish growing 6 to 22x with history** (1.4 to 10 s run, 6 s deliver,
   5.8 s settle at height 600): owner hot-path (activity cell cost, law 17).
4. **certify 25 s and restart 12.5 s at height 620** (writes are halted while certify runs): hot-path.
5. **`credit` / any signed read costing 697 fsyncs and 19,808 syscalls, proportional to the member's refs**:
   a read should be near-free; exorcist (fsync-free retained read evidence, one attempt record instead of
   about 350 files) and hot-path (batch plan O(refs)).
6. **`POST /doc/new` 6.5 to 7.7 s, `doc new` 2.6 to 4 s, `create object` 2 to 3 s, `say` 1 to 1.7 s**: every
   write is 0.5 to 3 s of fsync wait; exorcist.
7. Web read pages 15 to 70 ms and public GET / 26 ms: acceptable relative to the above, still 15x to 70x the bar.

## Coverage map: every user-, agent- and operator-visible path

One row per path. Bar: about 1 ms of warm server-side work per action. "Cost" says how the number was
obtained: **M** = measured by me on b9450147f (b4), 1c151fce4 (b5) or 74e1cfa10 (b6), hbox load 9 to 15;
**E** = estimated from a measured neighbour, stated; **0** = not measured at all. "Grows" = grows with
history (h = chain height / entries / refs). Owner is one of the live lanes (hot-path a6c4a1532687a4fdb,
exorcist a76808829fc8e4836, perf-client a778bbda6509944a5, perf-apps a25df305cfd551d8b, private-cells
a8da2b953507b402b, retained-mode a13f0c9ab4513b2d7, app-reds ad85d40779880420c), a *proposed* one where I
am inferring a lane's scope from its name, or **UNOWNED**.

### Shell and client

| path | warm cost | grows | owner |
|---|---|---|---|
| ssh forced command + wrapper (`mini-shell-ssh`) | M: client floor 7 ms (`help`); b4 13 execs, b5 22 (cold residents), b6 wrapper `#!/bin/bash` and mkdir/flock gone | no | exorcist (done in b6), perf-client |
| signed read `credit`, `read`, `can`, `refs` | M: b4 650 ms to 13 s (128 refs); b5 211-427 ms; b6 211-256 ms | b4 yes (refs); b5/b6 flat in refs | exorcist (fsync), retained-mode (proposed), hot-path |
| stream read `tail -n N` | M: b4 2.0-2.6 s; not re-measured since | b4 modest | hot-path, perf-client (proposed) |
| `history`, `why`, `inspect`, `describe`, `law show`, `inbox` | 0 (local file reads, plus one Host read for `inspect`) | E: yes with attempts (698 retained attempts) | UNOWNED |
| first signed read of a new session | M: 20.7 s (b3), 0.5-0.8 s (b5) | fixed | hot-path (done) |
| idle member's first action after hundreds of heights | M: 19-61 s (b4), 0.36 s (b5) | fixed | hot-path (done) |
| restart: wall and first read | M: 12.5 s at h620 (b4); 11.7 s wall + 0.24 s read at h491 (b5) | wall: yes | hot-path |

### Writes (every one is propose + submit)

| path | warm cost | grows | owner |
|---|---|---|---|
| `say`, `topic`, `pin`, `react` | M: b4 1.1 s; b5 0.55 s; b6 0.4-0.5 s; 60% is Host op2 (163 ms) | modest | hot-path (op2), exorcist |
| `doc new` / `append` / `submit` / `show` | M: 2.6 s / 0.9 s / 0.9 s / 0.5 s (b4); append+submit 1.0, 2.1, 3.4 s at 13/103/303 entries (b6) | **yes** (event-log cell, O(history)) | private-cells (FORMAT a), hot-path |
| doc `edit`, `insert`, `move`, `remove`, `mark`, `link`, `transclude`, `annotate`, `search`, `diff`, `history` | 0 (E: each is one propose+submit like append, so >= 1 s) | E: yes | private-cells (proposed) |
| `create` object, `provision` | M: 2-3 s (b4); 1.3-2.1 s (b6); 3.5 s avg for 128 in b5 | no | hot-path, exorcist |
| `chat new` / `invite` / `join` / `enter` | M: 8-14 s / 21 s (invite+join) (b4); chat new 10 s at load 13 (b4 batch) | chat new yes | hot-path, exorcist |
| `story new` | M: 28-45 s (b4); 14 s (b5); 7.0 s (b6) | yes (b4) | hot-path (row 12, FORMAT batch) |
| story `go` / `take` / `act` / `narrate` / `look` | M: ~1.0-1.7 s each on b1 (early run); not re-measured | no | UNOWNED |
| `delegate` / `revoke` + submit + publish + import | M: 0.9 + 1.8 + 0.3 + 0.4 s (b4); delegate+submit 1.7-3.1 s at 13, 3.9-4.5 s at 303 grants | **yes** (authority cell) | hot-path (authority fix), private-cells (FORMAT a) |
| `room kick`, `seal`, `rotate`, `rewrap`, `renew`, `welcome`, `concierge`, `leave` | 0 (E: >= 1 s each) | E: yes | UNOWNED |
| `law` install / check, `kind`, `program`, `instance call/set` | 0 | E: yes | UNOWNED |
| private rooms (`chat new --private`, key wraps) | 0 (E: >= chat new 8 s plus ML-KEM wraps) | E: yes | private-cells |
| `market` / `bid` / `reveal` / `settle`, `job` verbs, `board` | M: `market open` 2.4 s (early); `job`, `board`, `bid` 0 | E: yes | UNOWNED |
| `key set/grant/revoke`, `credit`/`tariff`/`topup`/`pay ROOM` | `credit` M 0.2 s; `tariff` M 1.9 s (b1); `topup`, `pay ROOM`, `key` 0 | no | UNOWNED |
| `pay status`, `pay address`, `pay audit` | M: 0.7-1.2 s (b4); `audit` 0.2 s | no | UNOWNED (pay-watcher side: 0) |

### Programs

| path | warm cost | grows | owner |
|---|---|---|---|
| `bend publish` / `run` / `answer` / `deliver` / `settle` | M (b4, fresh -> aged h600): publish 0.9 -> 6.4 s; run 1.4 -> 7.3 s; deliver 1.1 -> 6.1 s; settle 0.27 -> 5.8 s; answer 0.17 s | **yes, 5-22x** | hot-path (authority fix a55855f18, in batch 7) |
| `bend await` / `show` / `lookup` | M: 0.2 s | no | hot-path |
| default purse (cost per completed tally) | M: net 91,338 after settle | n/a | hot-path (done) |

### Web (gateway on loopback, one helper)

| path | warm cost | grows | owner |
|---|---|---|---|
| read pages `/ /doc /story /room /bend /verb /tour /export` | M: 14-33 ms | E: mild | perf-client |
| `/apps`, `/receipts` | M: 41-50 / 45-68 ms | E: yes (698 attempts) | perf-client, perf-apps (`/apps`) |
| form POSTs (`/doc/new`, append, verb forms, re-POST replay) | M: `/doc/new` 6.5-7.7 s (b4); append 0.6 s; replay 0.09 s | as the verb | hot-path / perf-client |
| login + terminal (`/login`, `/term` WebSocket) | 0 | E: no | perf-client (proposed) |
| public reader `GET /` anonymous | M: 26 ms warm, 77 ms first; cold body start `J-COLD-READ` once 133 s then 2 s | no | perf-client (proposed) |
| `/search` | 0 (answered 400 without a valid query) | E: yes | UNOWNED |

### Apps, Hermes, agents

| path | warm cost | grows | owner |
|---|---|---|---|
| `apps search`, `list`, `show`, `status`, `open` | M: `apps list` 4 ms (pending install), `search` fast (file) | E: no | perf-apps |
| `apps install` end to end | M: 1,243 s run for 2 installs (b6), still red (START UNRESOLVED); perf-apps reports 39.5 -> 17.7 s | n/a | perf-apps, app-reds |
| app start, route, first page through the grain front | 0 (blocked by the START red) | E: no | app-reds, perf-apps |
| app request/response through the broker (beneath-HTML write) | 0 | 0 | perf-apps (proposed) |
| `summon`, `dismiss` | 0 (no Hermes in scratch worlds) | 0 | app-reds |
| Hermes `ask` to reply: Host side, model call (external), reply turn | 0 (forge: refused `no-credential`) | 0 | app-reds; model time reported separately as external |
| Hermes typed tool call (Davros etc.) | 0 (gate row passes but is not timed) | 0 | app-reds, perf-apps |
| `key` / provider routing, inference scheduler | 0 | 0 | UNOWNED |
| agent session overlay, `agent-session-overlay.sh`, resident start | 0 | 0 | UNOWNED |

### Operator, infrastructure and external

| path | warm cost | grows | owner |
|---|---|---|---|
| certify / checkpoint | M: 0.8-6.6 s (b5, 256 tail); 25 s at h620 (b4) | b4 yes | hot-path |
| mini-health (signed sponsor read) | M: 0.2-8 s (b2-b4 depending on restart) | b4 yes | hot-path |
| clock tick (`mini-clock-tick`), roster sync, door tick | 0 | 0 | UNOWNED |
| door `/join`, enrol, `mini-reenroll`, invite, link | 0 (door held closed; scratch worlds enrol directly in ~3 s per member: world-up for 5 members is ~60 s) | E: no | UNOWNED |
| Discord bridge (`discord-entrance`, mirror, `mini-discord`) | 0 | 0 | UNOWNED |
| `pay-watcher` (chain tick, credit) | 0 | 0 | UNOWNED |
| carry (RECEIPT-CARRY, carry verifier, edge seal) | 0 | E: yes (prefix verification) | UNOWNED |
| fn / FN consumer (FN-E1, E2, selective origin) | 0 | 0 | UNOWNED |
| evidence capture and export (`export world`, `doc app-export`, backup, `mini-restore-check`) | `export world` M 6.9 s at h195 (early); others 0 | **E: yes** (O(world)) | UNOWNED |
| consensus and source agreement (SOURCE-AGREEMENT-READER, joint-agreement-crypto, joint `consensus pin`) | 0 | E: yes | UNOWNED |
| snapshot save / restore, cold start | 0 (designed; snapshots not exercised) | the point of the work | hot-path (cold-start), retained-mode (proposed) |
| world-down / teardown leaving residents | defect, not latency | n/a | infra (outside the lanes) |

## Coverage map, second pass (b6 74e1cfa10, scratch world, hbox load 9 to 12, via ssh, ms, three runs)

The previous map's `0` rows that a scratch world can reach are now measured. Every number includes the ssh
connection and wrapper: a pure local verb (`help`) costs **180-200 ms over ssh against 7 ms for the same client
called directly**, so about 175 ms of every ssh-carried action is the ssh path itself (connect, forced command,
bash wrapper), before any Host work. That floor is 175x the bar and applies to every row of the shell table.

| path | warm (ms) | grows | owner |
|---|---|---|---|
| ssh + wrapper floor (`help`) | 179-203 | no | perf-client |
| local read-only verbs (`history`, `history all`, `why`, `inbox`, `refs`, `room list`) | 180-230, same at 0 and 132 retained attempts | **no** (flat to 132 attempts) | perf-client (floor only) |
| `inspect caps` / `can REF` | 207-389 / 216-219 (one Host read) | no | perf-client |
| story `look` / `go` / `take` / `act` / `narrate` | 280-453 look; 593-629 for `go`/`take`/`act`; 435 narrate; `story list`/`law tale` 184-214 | not seen over 5 moves | hot-path |
| room `new` / `members` / `status` / `invite` + submit / `kick` + submit | 1,001 / 464 / 206 / 245+492 / 396+704 | not measured with history | hot-path |
| `law check` / `law show` / `inspect law` / `law install` + submit | 194 / 471 / 512 / 211 + 839 | not measured | hot-path |
| `market open` / `bids` | 2,255 / 455 | not measured | UNOWNED |
| `board new` | 761 (`board add` needs a numeric TASK: my test row was a usage error) | not measured | UNOWNED |
| `jobs`, `tariff show`, `tariff set`, `credit` | 183 / 445 / 386 / 560 | no | UNOWNED |
| `pay audit`; `pay status` | 206; usage error without the account ref | no | UNOWNED |
| `key ls`, `key providers` | refused: `mini-keys refused client-config` (a scratch world has no keys broker) | n/a | UNOWNED (needs a world with mini-keys: the forge) |
| `export world` | 1,034 first, 176 second, at height 142 (6.9 s at h195 in an early run on another box) | E: yes with world size | retained-mode inventory |

No scratch-reachable row is near 1 ms; all are 180 ms to 2.3 s, 175 ms of which is the ssh path.

## Owners after the coordinator's ruling

- hot-path (a6c4a1532687a4fdb): story play verbs (280-629 ms), room administration (206 ms-1 s), `law` verbs (194 ms-840 ms).
- perf-client (a778bbda6509944a5): the local read-only verbs (all flat at 180-230 ms: the 175 ms ssh/wrapper floor, not the verb), the ssh path itself, door/enrol/reenroll once measured.
- retained-mode inventory (a13f0c9ab4513b2d7): `export world`/app-export/backup/restore, carry, fn consumer, consensus and source-agreement readers, as migration targets (carry/fn/consensus: still 0 measurements).
- Measure first, owner after: Discord bridge and pay-watcher (forge only), door/enrol (forge), `market`/`board`/`jobs`/`tariff`/`pay`/`key` verbs (above; no owner named yet), `/search`, inference scheduler, agent session overlay.

## Open items

- Re-run on a quiet box (no other tenants) to get honest fsync cost; with 697 fsyncs even at 0.1 ms the
  `credit` read is 70 ms.
- Measure Hermes ask to reply, typed tool call, apps install/start/first page, and door enrol on the forge
  once apps installs go green (Simple Todos still `routing` no-grant on b9450147f).
- The revoke and bend await/answer/deliver rows of `tm.sh` were broken by my own variable clobber and need a
  rerun; the strace transcripts are `hbox:~/xp/st.credit.txt`, `st.chatnew.txt`, `st.say.txt`; the raw table
  is `hbox:~/xp/timings.tsv`; the CPU table is `hbox:~/xp/bd2.out`.
