# User action timings (batch 4, b9450147f)

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

## Open items

- Re-run on a quiet box (no other tenants) to get honest fsync cost; with 697 fsyncs even at 0.1 ms the
  `credit` read is 70 ms.
- Measure Hermes ask to reply, typed tool call, apps install/start/first page, and door enrol on the forge
  once apps installs go green (Simple Todos still `routing` no-grant on b9450147f).
- The revoke and bend await/answer/deliver rows of `tm.sh` were broken by my own variable clobber and need a
  rerun; the strace transcripts are `hbox:~/xp/st.credit.txt`, `st.chatnew.txt`, `st.say.txt`; the raw table
  is `hbox:~/xp/timings.tsv`; the CPU table is `hbox:~/xp/bd2.out`.
