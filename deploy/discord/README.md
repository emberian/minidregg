# Discord entrance

`mini-discord` lets a member use Mini from Discord. It adds no verbs:

- A Discord user maps to one Mini session through the root-owned roster, and the session's key is held on
  the box, as it is for the ssh entrance.
- `/mini <line>` hands the line to `mini shell --line`, through the same forced command
  (`mini-shell-ssh`, the candidate's `bin/mini-line`) that ssh uses.
- `/mini-help` runs the shell's own `help`.
- `/mini-world [target:NAME] [page:N]` presents the native `home --json` member projection. A displayed action
  is not a grant; actions are ordinary `/mini` lines judged by Mini.
- `/mini-status target:INTERACTION-ID` reads that Discord user's retained interaction custody. A different
  Discord user cannot inspect it even if mapped to the same session.
- `/mini line:link CODE` is how a Discord user gets on the roster (below, "Linking").

It takes interactions one of two ways (`MINI_DISCORD_MODE`):

- **HTTP** (the default): an interactions endpoint. Discord POSTs each signed slash command to the
  application's Interactions Endpoint URL and the entrance answers. No bot token, no gateway.
- **Gateway**: for an application whose endpoint URL is unset (the demo's Dragon's Egg, whose owning
  account can no longer set it). The bot connects out to `wss://gateway.discord.gg` with its token and
  intents 0, takes `INTERACTION_CREATE` there, and answers through
  `POST https://discord.com/api/v10/interactions/{id}/{token}/callback`. The token is a systemd
  credential (`MINI_DISCORD_BOT_TOKEN_FILE`), never in the environment. No signature check is needed: the
  TLS connection the bot opened is the authentication. Install: `INSTALL.md`.

Both modes feed the same handler: everything below (roster, line rules, deferral, custody, the runner)
is identical.

```
Discord ──HTTPS──▶ Caddy on the box (/interactions) ──HTTP──▶ 127.0.0.1:8793 mini-discord      (HTTP mode)
Discord ◀──WSS (bot connects out)── mini-discord; replies: POST discord.com/…/interactions/ID/TOKEN/callback (gateway mode)
                                                                  │  roster: discord id -> NAME
                                                                  ▼
                  mini-session-run (root, socket-activated) ──▶ mini-shell-ssh … as mini-s-NAME, SSH_ORIGINAL_COMMAND=<line>
mini-discord ──curl PATCH /webhooks/APP/TOKEN/messages/@original──▶ Discord    (the answer)
```

## What one command does

1. **Signature** (HTTP mode). `X-Signature-Ed25519` must verify (`verify_strict`) over
   `X-Signature-Timestamp || body` under the application's public key, and the timestamp must be within
   300 s; otherwise **401**. Gateway mode skips this: events arrive on the bot's own TLS connection.
2. **PING** gets PONG (HTTP mode; the gateway sends none).
3. **Roster.** The roster file must be owned by root and not writable by group or others; a file that fails any
   check answers no one. An unlinked Discord user is told where the door is (`MINI_DISCORD_DOOR_URL`) and
   nothing runs.
4. **Line.** At most 1000 characters, one line, no control character; at most 4 lines run at once across
   sessions, and the lines of one session run one at a time.
5. **Deferral, then custody, then the run.** The entrance answers `DEFERRED` (type 5, ephemeral) before any
   fsync: `handle` only takes the interaction's custody lease. Only after the deferral is on the wire is the
   acceptance retained, and a line whose acceptance cannot be retained does not run. (An fsync before the
   deferral could miss Discord's 3 s window; the user then saw "This interaction failed" and re-issued the
   line under a new interaction id, which ran it twice.) The started phase is retained before running.
   - The same interaction id with the same binding returns the retained answer and never runs again; a changed
     binding is **409**. An accepted-but-unstarted interaction may run on a retry of the *same* interaction.
   - A started line without a retained outcome is **UNKNOWN** and is never rerun. An answer that does not come
     back from the runner is `undecided`, never a resend. Settle effects with the shell's own `history`,
     `lookup ID` and owner-specific recovery commands.
   - The answer PATCHes `@original` with the shell's stdout (cut to 2000 characters), or the shell's own
     ending line (`error:` / `usage:` / `refused:` / `undecided:`). An unsuccessful PATCH does not rerun the
     line; `/mini-status` shows the result.
6. **Log.** `(user, line, ending, exit)` is appended to `MINI_DISCORD_STATE/log/NAME.discord.log` (0600).

Every answer is **ephemeral** in Discord (visible to the invoking user in the Discord UI); its content is still
disclosed to Discord and to the operator. Every answer sets `allowed_mentions: {parse: []}`.

## Split tenancy: the runner socket

Under split tenancy (dregg-infra `/etc/mini/tenancy` = `split`) each member's session is its own account
`mini-s-NAME`, and the entrance is account `mini-discord`, which cannot run anything as a member by itself.
It connects to the root runner's socket `/run/mini-session-run.sock` (`MINI_SESSION_RUNNER`), which only
root and group `mini-discord` may open, and sends `NAME\nLINE\n`. systemd starts one
`mini-session-run@.service` per connection, as root; the runner checks that NAME is a value of the root-owned
Discord roster and that `mini-s-NAME` exists in group `mini-hosted` with its own 0700 home, runs the same
forced command as `mini-s-NAME` with a fixed environment and its own timeout, and answers
`mini-session-run-v1 EXIT OUTLEN ERRLEN\n` followed by both streams.

No setuid program is involved, so the entrance keeps `NoNewPrivileges=yes` and `RestrictSUIDSGID=yes` under
split tenancy as well (the earlier `sudo` runner needed both lifted). A compromised entrance can act as a
rostered member only through the shell's grammar, never read a member's files, and never act as a member who
is not on the Discord roster. The runner and its units are dregg-infra's; their source is in
`deploy/door/infra/` with the install steps.

The line reaches the shell as one argument (`--line "$SSH_ORIGINAL_COMMAND"`) with an otherwise empty
environment and never reaches a system shell. NAME alone chooses the workspace and home
(`sessions/NAME/workspace`, `sessions/NAME`). The follow-up URL contains the interaction token, so it reaches
`/usr/bin/curl` on stdin and never argv; the body goes through a 0600 spool file removed after the call.

## Linking: the roster is the door's

Nobody edits the roster by hand on the demo box. A stranger who joins at `demo.dregg.online/join` and ticks
"link Discord" gets a one-time code on their status page. In Discord they type `/mini line:link CODE`. The
entrance, which only proves the Discord id (the signed interaction), writes one bounded request to the door's
link spool (`MINI_DISCORD_DOOR_LINKS`, default `/var/lib/mini-discord/door-links`, at most 64 pending) and
answers at once. The door's root processor matches the code to its account and is the only writer of
`/etc/mini/discord-roster.json`. A code is single-use, expires after `linkTtlHours` (default 168, `mini-door-process.rs:129`), can never map to the sponsor or an
operator name, and a Discord id already on the roster is refused (`deploy/door/README.md`).

## Retention

- Completed interaction custody (`MINI_DISCORD_STATE/custody/`) is removed after `MINI_DISCORD_CUSTODY_DAYS`
  (default 7) or beyond the newest `MINI_DISCORD_CUSTODY_MAX` (default 2000), checked after every line. A
  record keeps at most 64 KiB of each stream. Accepted and started records are the evidence of an undecided
  line and are never removed.
- A line log is rotated to `NAME.discord.log.1` past 1 MiB (one generation kept).
- A session's `refusals/` keeps the newest 256 retained refusals (`mini shell`).
- Custody is session data: protect `MINI_DISCORD_STATE` like keys. The interaction token is never retained.

## Making it live on the demo box

**The demo runs gateway mode with Dragon's Egg: `INSTALL.md`.** The steps below are HTTP mode, for an
application whose endpoint URL we can set.

dregg-infra's `install.sh` installs the binary from the candidate, the unit (`mini-discord.service` here) with
its split drop-in, and the runner. ember's part:

1. **The application.** At <https://discord.com/developers/applications>, New Application; copy the
   Application ID and Public Key into `/etc/mini/discord.env` (`discord.env.example`, root:root 0600,
   installed by dregg-infra's `install.sh`).
2. **Commands.** From ember's machine (the bot token is used once and never stored on the box):
   ```sh
   curl -X PUT -H "Authorization: Bot $TOKEN" -H 'Content-Type: application/json' \
     --data @deploy/discord/commands.json https://discord.com/api/v10/applications/$APP_ID/commands
   ```
3. **Endpoint.** Set Interactions Endpoint URL to `https://demo.dregg.online/interactions`. Discord sends a PING
   and a badly signed request; saving succeeds only on PONG and 401. Caddy's route is in
   dregg-infra (`edge/demo/host/caddy/Caddyfile`, not in this repository).
4. **Install.** Add the app to a server with `applications.commands`, or allow user install.

## The room mirror (off on the demo)

`mini-discord-mirror` bridges one public room and one channel, both ways. It is **not** part of the demo's
Discord path, and it starts only with `MINI_MIRROR_PUBLISH_ROOM_TO_CHANNEL=yes`. It needs what the entrance
does not: a bot user with the **Message Content** privileged intent and Read Message History, and the channel
webhook. Those secrets live with the key broker (`mini-keys`, `/var/lib/mini-keys/discord-mirror.json`), which
posts and reads for the mirror; the mirror's environment never holds them, and it exits 78 if
`MINI_MIRROR_WEBHOOK_URL`, `MINI_MIRROR_CHANNEL_URL` or `MINI_MIRROR_BOT_TOKEN` is set.

- **Environment:** `MINI_MIRROR_PUBLISH_ROOM_TO_CHANNEL=yes`, `MINI_MIRROR_ROOM`, `MINI_MIRROR_HOME`,
  `MINI_MIRROR_WORKSPACE`, `MINI_MIRROR_INTERVAL_S` (minimum 5, default 30), `MINI_MIRROR_BROKER` (default the
  broker's client config), and the forced-command variables above.
- **A private room is never mirrored.** The feed is read only through `PublicFeed`, which refuses a header or
  entry that says private or says nothing; a private room stops the bridge (exit 78).
- **Room to channel:** signed `tail --discover` pages, per-stream cursors, at most 20 entries a poll, posts
  paced 1.1 s apart. Each post is a delivery record retained before the send. A 2xx completes it. **An
  answered non-2xx (a 429 rate limit, any refusal) means Discord took nothing: the record returns to a startable
  state with a 30 s doubling backoff (capped at 1 h), and later entries wait behind it so the channel keeps room
  order.** Only a send whose answer was lost is UNKNOWN; after locating the message, the operator records it
  with `mini-discord-mirror --resolve-up CELL SEQUENCE DISCORD_MESSAGE_ID`.
- **Channel to room:** backward REST pages to the old watermark, drained oldest first, at most 20 a poll; each
  person's message becomes `say --via discord` with an operation record, signed by the bridge.

## Tests

```sh
cargo nextest run -p minidregg-discord-entrance -E 'binary(endpoint) | binary(gateway) | test(session::) | test(door::)'
```

`binary(gateway)` drives gateway mode against a fake gateway: HELLO, IDENTIFY (token, intents 0), READY,
an INTERACTION_CREATE answered through the callback and a deferred follow-up, the heartbeat's sequence,
RECONNECT then RESUME, INVALID_SESSION then a fresh IDENTIFY, and a missed ACK then RESUME. The others
exercise signed HTTP interactions, deferral-before-custody, persisted restart and UNKNOWN handling,
actor-bound status, revocation, linking, retention, and the runner socket protocol against a stand-in. The
mirror's tests start a real key broker and need Linux. `tests/native-world.py` composes a fake signed Discord
with the actual entrance and a fresh native Host/Store; its mirror rows still set `MINI_MIRROR_WEBHOOK_URL`,
`MINI_MIRROR_CHANNEL_URL` and `MINI_MIRROR_BOT_TOKEN` (`native/discord-entrance/tests/native-world.py:108`),
which the mirror refuses with exit 78 (`mini-discord-mirror.rs:397`), so those rows do not pass.

`/feedback text:...` files a report: the member's own `feedback --via discord "TEXT"` line, one signed turn in the member's
`feedback` room (readable by the operator only). Register it from `commands.json` with the other commands.
