# Fleet surface on Mini — journey and contention, 2026-09-30

One fresh, private persvati Store per run; nothing copied from another Store.
The contract is [`docs/FLEET-SURFACE.md`](../../FLEET-SURFACE.md). Every
service a script started was stopped (checked after each run: zero `mini
serve` processes for the client below).

| Item | Pin |
| --- | --- |
| Host | `minidregg-host-fe433a1-r6`, SHA-256 `4f6d865a6b963399e04a84b232424ae02e2badf6ccfdc756ca349c1a3991ea17`, built by `scripts/build-native-host.sh --incremental-suffix-from` the qualified `e22d16b` build (`native-e22d16b/build-r3`; Lean sources of the closure identical to `abe988d`), 101 compiled modules, 451 s |
| Mini client | `mini-fa0a908`, SHA-256 `ddb777fe75d6213428d3e77010d8bf97369b93be49d0f54a6e7e04d222e37e23`, `cargo build --release --locked --bin mini` at `fa0a908` |
| SQLite Store helper | SHA-256 `ad03aede839259c1884383fc97f141a3fe106ba2f2cbae0df6f7916676fe193f` (the qualified helper of the 2026-09-28 enrollment evidence) |
| Ed25519 verifier | SHA-256 `c84004123ae6f02654cb6749e4105e351199618aaefce5755a2a0bb10bd0892b` (same) |
| Scripts | `native/resource-client/fleet-journey.sh`, `native/resource-client/fleet-contention.sh` at the commit that adds this file |

The host is `fe433a1`; the client source is unchanged between `fa0a908` and
`fe433a1` (the later commits touch Lean only).

## Journey (`journey/`)

`fleet-journey.sh HOST MINI STORE VERIFIER run/j8`: fresh genesis (sponsor
subject 7, account 7 with 100000, tariff base 3), two agents, every verb,
every refusal pole, cold restart. Wall 80.6 s. Each step's stdout is
`journey/STEP.json`; refusal poles keep their stderr.

| Step | Verb | Seconds | Result | What it shows |
| --- | --- | ---: | --- | --- |
| fixture | genesis + serve + sponsor workspace | 27.208 | ok | fresh Store (newparticipant fixture) |
| join-a | join | 7.616 | ok | key admitted (record 1), owned account born and funded 1000 from account 7 (record 2) |
| join-b | join | 8.233 | ok | same, funded 500 (records 3, 4) |
| send | send | 2.126 | ok | one turn: event `inbox`#1 + pay 7 to agent-b + fee 3 (record 5) |
| transfer | transfer | 2.143 | ok | one turn: 25 to agent-b + fee 3 (record 6) |
| receipt-by-transaction | receipt | 0.142 | ok | op 98 returns send's exact receipt |
| receipt-by-head | receipt | 1.087 | ok | op 97: 2 fleet turns paid by agent-a, head = transfer's receipt |
| receipt-by-attempt | receipt | 0.243 | ok | op 95 from the retained ingress: `replayed`, same receipt |
| publish-1 | publish | 2.342 | ok | event `news`#1 (record 7) |
| publish-2 | publish | 2.596 | ok | event `news`#2 (record 8), parent = #1 |
| poll-news-0 | poll | 1.348 | ok | since 0: both events, exact payloads, head 2 |
| poll-news-1 | poll | 1.375 | ok | since 1: event #2 only |
| poll-news-2 | poll | 1.216 | ok | since 2: none, cursor stays 2 |
| poll-inbox | poll | 1.366 | ok | the send's event carries the send's transaction id |
| grant-propose | delegate | 3.000 | ok | agent-a proposes an observe-only grant on its account for agent-b |
| grant-submit | delegate | 2.206 | ok | existing delegation receiver admits it |
| grant-publish | delegate | 0.386 | ok | recipient reference with exact receipt |
| subscribe-poll | poll | 1.416 | ok | **agent-b** reads agent-a's `news` with the delegated grant: same events |
| observe-only-spend | transfer | 2.244 | refused | plan released (agent-b may observe); **the receiver** refuses: `FleetTurn.Reject.capabilityRejected` |
| read-a | read | 1.015 | ok | agent-a balance 956 = 1000 − 7 − 25 − 4 × 3 |
| read-b | read | 1.089 | ok | agent-b balance 532 = 500 + 7 + 25 |
| overdraw | transfer | 1.473 | refused | plan refuses: `FleetTurn.Reject.bookRefused` |
| foreign-spend | transfer | 1.199 | refused | agent-b names agent-a's account and grant: signed observation refused |
| foreign-poll | poll | 0.904 | refused | same names, read: signed observation refused |
| receipt-absent | receipt | 0.130 | refused | transaction id 1: `absent` |
| receipt-after-cold-open | receipt | 4.182 | ok | service restarted; first request pays the cold open, which re-admits all 9 accepted records (four fleet turns among them) through `NativeHostReplay`; transfer's receipt unchanged |
| poll-after-restart | poll | 1.233 | ok | events identical to before the restart |

## Contention (`contention-k2-r8/`, `contention-k4-r5/`)

`fleet-contention.sh HOST MINI run/j8 K R`: joins K fresh agents on the
journey's Store (fund 1000 each), then R rounds in which all K publish at
once. `turns.tsv` has per-turn wall seconds, re-plans and result;
`rounds.tsv` has per-round wall seconds.

| Agents | Rounds | Turns | Admitted | Re-plans | Mean turn s | Max turn s | Wall s | Admitted / s |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 2 | 8 | 16 | 16 | 8 | 8.234 | 13.245 | 85.854 | 0.186 |
| 4 | 5 | 20 | 20 | 30 | 32.035 | 62.811 | 240.565 | 0.083 |

Every round admitted every turn, with exactly `0 + 1 + … + (K − 1)` re-plans:
each commit stales every other agent's in-flight plan, so the k-th agent to
land re-plans k − 1 times. Before `4a33c88` the losing turn surfaced as
`signature (envelope staleAuthority)` (8 of 8 rounds refused one of two
agents; run j6, not retained here); `4a33c88` reports it as the Host's typed
`contention` and the client re-plans in a fresh attempt. Before `fe433a1`
fleet submit reopened the whole Store to seal each receipt; the same K=2
probe then took 26 → 46 s per round (run j7, not retained here); now 7.6 →
13.3 s. Round time still grows with history (every request rereads and
decodes the whole durable image), and throughput falls as agents are added,
because a losing plan's ~15 Host requests are wasted work on the one
serialized Host process.

## What this does not show

- A second node, or any network transport: one Host process behind one
  owner-private Unix socket.
- Throughput on an idle box: persvati carried other lanes' Lean builds (load average about 6 during these final
  runs, up to 35 earlier in the session).
- Crash recovery between the submit marker and the answer (the lookup path is
  exercised only on a completed turn).
- The collector's balance: no journey subject holds a grant on account 99;
  conservation is the Book's proved law, and the payer side is checked
  exactly.
