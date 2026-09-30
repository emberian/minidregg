# The Discord entrance on a fresh private Store, 2026-09-30

`discord-entrance.sh` bootstraps a fresh private Store and runs `mini serve` (MR's recipe: `native/resource-client/newparticipant-acceptance.sh` with MR's qualified binaries). It then starts two services:

- `mini-discord` on 127.0.0.1:28793;
- the loopback fake of Discord's webhook API (`examples/fake-discord api`) on :28794.

The fake's signer (`fake-discord interact`) sends signed slash-command interactions, shaped as Discord sends them, to `POST /interactions`.

**No real Discord was involved.** The application key is a fresh test key made by `fake-discord keygen`, and `MINI_DISCORD_API_BASE` points the follow-up PATCH at the fake. Everything else is the deployed shape:

- The real `mini-shell-ssh` forced command, with the line in `SSH_ORIGINAL_COMMAND`.
- The real `mini shell --line`, the Host, the Store and `/usr/bin/curl`.
- A roster file and session homes laid out as on the box. The sponsor is `ember`, with the sponsor workspace; the friend is `friend`, with `sessions/friend/workspace`.

Run 2 (`run-2/`) was made on persvati from branch `mini-discord` at d4892050. It has 27 rows and 0 failures, and all three services were stopped afterwards (`run-2/cleanup.txt`: "processes naming the run directory after cleanup: none").

## Reading the table

- **ack s** is the wall time until the interaction's own HTTP response. It is always a few milliseconds.
- **follow-up s** is the time until the fake received the `PATCH …/messages/@original`.
  - Row 17 (a `create`, which is a real Host turn) took 4.5 s. That is above Discord's 3 s limit, so the deferred path is required, not optional.
  - Run 1 measured 6.8 s for the same row.
- **answer** is exactly what the user would see:
  - for a `now` row, the type-4 `data.content`;
  - for a `deferred` row, the PATCHed `content`;
  - for a 401 row, the HTTP body.

  Code fences are stripped here. Full bodies are in `run-2/NN-*.answer`, `*.body` and `*.followup.json`.

| n | who | command | line | expect | HTTP | type | ack s | follow-up s | verdict | answer (verbatim; long JSON cut at 150 chars here) |
|---|---|---|---|---|---|---|---|---|---|---|
| 1 | discord | /pong | `` | pong | 200 | 1 | 0.004 | - | ok | {"type":1} |
| 2 | sponsor | /mini | `refs` | 401 | 401 | - | 0.004 | - | ok | invalid request signature |
| 3 | stranger | /mini | `refs` | now | 200 | 4 | 0.003 | - | ok | error: Discord user 1400000000000000999 is not on this Mini's roster; nothing ran. Ember must add you: send ember this id. |
| 4 | friend | /mini | `keygen k1` | deferred | 200 | 5 | 0.003 | 0.119 | ok | cd7d2a8661920c75226817c005b020fc9073c2d6def9346525886275890e2885 |
| 5 | check | | k1 secret and public key exist only in the friend's session home | | | | | | ok | |
| 6 | sponsor | /mini | `refs` | deferred | 200 | 5 | 0.004 | 0.068 | ok | {   "authority": "discovery-only",   "references": [     {       "authority": "hint-only",       "controlCapability": "53",       "kind": "object",    … |
| 7 | check | | sponsor refs lists factory (target 10) | | | | | | ok | |
| 8 | sponsor | /mini | `read nope` | deferred | 200 | 5 | 0.004 | 0.067 | ok | error: cannot inspect /home/ember/build/mini-product-20260930/mini-discord/run/de-2/store/sponsor/refs/nope.json: No such file or directory (os error  … |
| 9 | friend | /mini | `init k1 4242424242` | deferred | 200 | 5 | 0.004 | 0.119 | ok | /home/ember/build/mini-product-20260930/mini-discord/run/de-2/sessions/friend/workspace |
| 10 | friend | /mini | `import stolen object 10 54` | deferred | 200 | 5 | 0.004 | 0.120 | ok | stolen |
| 11 | friend | /mini | `read stolen` | deferred | 200 | 5 | 0.004 | 0.487 | ok | refused: unknown-key: this key is not enrolled on this Host (phase observation) (Host refused challenge, reply byte 255) |
| 12 | check | | friend's read of the sponsor's cell is the Host's refusal, verbatim | | | | | | ok | |
| 13 | friend | /mini | `read xxx…x (1001 characters)` | now | 200 | 4 | 0.004 | - | ok | usage: the line is 1001 characters; the limit is 1000 |
| 14 | friend | /mini-help | `` | deferred | 200 | 5 | 0.004 | 0.065 | ok | Every verb is one client operation; the Host decides. Words: 'literal', "escaped", {json} or [json], @FILE (HOME/requests/FILE).   whoami     whoami   … |
| 15 | sponsor | /mini | `whoami` | deferred | 200 | 5 | 0.004 | 0.067 | ok | {   "authority": "discovery-only",   "home": "/home/ember/build/mini-product-20260930/mini-discord/run/de-2/sessions/ember",   "initialized": true,    … |
| 16 | sponsor | /mini | `whoami` | 401 | 401 | - | 0.003 | - | ok | replayed interaction |
| 17 | sponsor | /mini | `create shared declared {"type":"all","predicates":[]}` | deferred | 200 | 5 | 0.003 | 4.548 | ok | /home/ember/build/mini-product-20260930/mini-discord/run/de-2/store/sponsor/sources/create-shared.current/intent.bin {   "acceptedCount": "1",   "conf … |
| 18 | sponsor | /mini | `invoke w1 shared create 2 1` | deferred | 200 | 5 | 0.004 | 1.529 | ok | {   "authority": "requires-current-admission",   "delegation": null,   "effect": "none",   "intentPath": "/home/ember/build/mini-product-20260930/mini … |
| 19 | sponsor | /mini | `submit w1` | deferred | 200 | 5 | 0.004 | 1.530 | ok | {   "acceptedCount": "2",   "confirmation": "installed",   "eventId": "56845010809736958335030026160376921429373485104283041471479002199919998480405", … |
| 20 | check | | mirror poll 1 (exit 0) posted field 2 = 1 | | | | | | ok | |
| 21 | sponsor | /mini | `invoke w2 shared write 2 7 1` | deferred | 200 | 5 | 0.004 | 0.745 | ok | {   "authority": "requires-current-admission",   "delegation": null,   "effect": "none",   "intentPath": "/home/ember/build/mini-product-20260930/mini … |
| 22 | sponsor | /mini | `submit w2` | deferred | 200 | 5 | 0.003 | 1.211 | ok | {   "acceptedCount": "3",   "confirmation": "installed",   "eventId": "45935298449121642877682314161508729248125016289254017734342476496333570981949", … |
| 23 | check | | mirror poll 2 (exit 0) posted field 2 = 7 (was 1) | | | | | | ok | |
| 24 | check | | mirror poll 3 (exit 0) posted nothing new | | | | | | ok | |
| 25 | check | | every run line and every rostered refusal is in its session's discord.log | | | | | | ok | |
| 26 | check | | no interaction token or channel webhook secret appears in the entrance log | | | | | | ok | |
| 27 | check | | the spool is empty (every follow-up body removed) | | | | | | ok | |

## What the rows show

| Required | Row | Result |
|---|---|---|
| signed `/mini keygen k1` | 4 | deferred. The public key comes back. The secret is only in `sessions/friend/keys/` (row 5). |
| `/mini refs` | 6 | deferred. The sponsor's reference list comes back. |
| unrostered user | 3 | answered at once with a line naming their id and that ember must add them. Nothing ran and nothing was logged in any session. |
| bad signature | 2 | **401** `invalid request signature` (one signature byte flipped after signing) |
| `/mini read nope` | 8 | The shell's own ending line comes back verbatim. For a reference that does not exist, that ending is **`error:`** (the client could not find `refs/nope.json`; the Host was never asked), not `refused:`. |
| a Host `refused:` line verbatim | 11 | The friend (key `k1`, not enrolled) imports the sponsor's `factory` target and reads it. The answer is `refused: unknown-key: …` exactly as `mini shell` prints it. |
| line > 1000 chars | 13 | answered at once with `usage: the line is 1001 characters; the limit is 1000`, and logged in the friend's `discord.log` |
| deferred path | every `deferred` row | type 5 (ephemeral) at once, then a PATCH to `@original` |
| replay | 16 | the same interaction id again is **401** `replayed interaction` |
| mirror (runner) | 17–24 | Real turns go through Discord: `create`, then `invoke`/`submit` twice. `mini-discord-mirror --once` posts `field 1 = 0 / field 2 = 1`, then `field 2 = 7 (was 1)`, then nothing (`run-2/channel-*.json`). |
| log | 25 | `friend/discord.log` has 6 records and `ember/discord.log` has 8 (`run-2/*-discord.log`) |

## Glue and deviations

- `fake-discord` is evidence glue, not a deployed binary. It stands in for discord.com in two roles: signing interactions and receiving webhook calls.
- The roster owner is the running user (`MINI_DISCORD_ROSTER_OWNER_UID=$(id -u)`), not root, because the run is unprivileged. The code path that checks the owner and mode is the same, and it is unit-tested both ways.
- The mirror ran in the **sponsor's** session, reading the sponsor's own reference. In deployment the runner gets its own enrolled key and an observe grant delegated to it; the poll line is the same. I did not do that enrollment here.
- The friend was never enrolled. Its `init` uses subject 4242424242, the same stranger that MR row 39 uses. That is what produces the Host refusal.

## Binaries (`run-2/binaries.sha256`)

| Item | SHA-256 |
|---|---|
| Host `mr-refusals/bin/minidregg-host-mr-r1` | `f171bfb0…c568` (MR's) |
| `mini` (`mr-refusals/bin/mini-mr-r1`, copied) | `f33998ef…a09c` (MR's) |
| `mini-shell-ssh` (from `deploy/shell/` on this branch) | `508e9cc0…4ab5`, the same as deploy-1's vendored copy |
| `mini-discord` (d4892050, `cargo build --release --locked`) | `00202a19…2ab2` |
| `mini-discord-mirror` | `777b059e…a02e` |
| `fake-discord` (example) | `839a52d1…e445` |
| Store and verifier helpers | the bake-off durable copies `ad03…193f` and `c840…892b` |
