# Discord entrance

`mini-discord` lets a friend use Mini from Discord. It adds no new verbs:

- A Discord user maps to one Mini session through the roster, and the session's key is held on the box, as it is for the ssh entrance.
- `/mini <line>` hands the line to `mini shell --line`, through the same forced command (`deploy/shell/mini-shell-ssh`) that ssh uses.
- `/mini-help` runs the shell's own `help`.
- `/mini-world [target:NAME] [page:N]` presents the shared native `home --json` member projection. Unselected discovery is limited to that session's held references; selecting a target makes the native signed current-authority read. It shows source identity/head, object revision, resident state and retained recovery commands when the producer supplies them. Actions remain ordinary `/mini` commands judged by Mini; a displayed action is not a grant.
- `/mini-status target:INTERACTION-ID` reads that Discord user's retained interaction custody. Responses include this locator. A different Discord user cannot inspect it even if mapped to the same session.

It is a Discord **interactions endpoint**:

- Discord POSTs each signed slash command to an HTTPS URL, and the endpoint answers.
- There is no bot gateway, no websocket, no long-lived connection and no bot token on the box.
- Caddy on the anchor terminates TLS and proxies to the workhorse's private address.

```
Discord ──HTTPS──▶ anchor Caddy (discord.dregg.net) ──HTTP──▶ workhorse 10.10.1.10:8793 mini-discord
                                                                  │  roster: discord id -> NAME
                                                                  ▼
                        mini-shell-ssh MINI HOST CONFIG SOCKET WS(NAME) HOME(NAME)   SSH_ORIGINAL_COMMAND=<line>
                                                                  │
mini-discord ──curl PATCH /webhooks/APP/TOKEN/messages/@original──▶ Discord    (the answer)
```

## What one command does

1. **Signature check.**
   - `X-Signature-Ed25519` must verify, with `verify_strict`, over `X-Signature-Timestamp || body` under the application's public key. Otherwise the answer is **401**.
   - Discord tests exactly this when you save the URL.
   - A timestamp more than 300 s from now is also refused with 401.
   - The durable interaction ID binds application, Discord actor, roster session/workspace, exact line and navigation page. A changed binding is HTTP 409. Completed duplicates return the retained answer; they do not execute again.
2. **PING.** It gets PONG.
3. **Roster.**
   - The roster file must be owned by root and must not be writable by group or others. A file that fails any check answers no one.
   - A Discord user who is not on the roster gets, at once:
     `error: Discord user <id> is not on this Mini's roster; nothing ran. Ember must add you: send ember this id.`
4. **Line.**
   - The line must be at most 1000 characters and a single line. Otherwise the answer is `usage: …`, sent at once and logged.
   - At most 4 lines run at a time across sessions.
   - Lines of one session run one at a time. Thread mutex acquisition does not promise arrival order.
5. **Deferred answer.**
   - The entrance answers `DEFERRED` (type 5, ephemeral) within milliseconds.
   - The accepted request is synced before deferral; the started phase is synced before running. A retry can resume an accepted request that never started. A started request without a retained outcome remains UNKNOWN and is never automatically rerun. An arbitrary shell line can contain multiple native operations; use the retained native `history`, `lookup ID` and owner-specific recovery commands to settle those effects.
   - It then PATCHes `@original` with one of two things:
     - the shell's stdout in a code block, cut to 2000 characters with a note saying how much was shown;
     - on failure, the shell's own ending line verbatim (`error:` / `usage:` / `refused:` / `undecided:`).
6. **Log.**
   - `(user, line, ending, exit)` is appended to `SESSIONS/NAME/discord.log` (0600).
   - Full captured stdout/stderr (each bounded to 1 MiB), ending and delivery status are synced into `SESSIONS/.discord-custody/APP-INTERACTION.json`, mode 0600 in a 0700 directory. This is sensitive session data; protect it like session keys. The interaction token is not retained.
   - Cross-process advisory leases and synced atomic records prevent concurrent duplicate execution. Corrupt or inaccessible custody fails closed. Do not delete custody to retry an uncertain command.
   - The roster is checked at admission and again after waiting for a session worker. Removing/remapping a user prevents queued execution and future custody retrieval. Native capability revocation/current law still governs every actual native operation.
   - An unsuccessful PATCH does not rerun the command. Its result remains available by status or signed interaction retry. There is no autonomous token-based reply recovery after restart; tokens are not retained.

Every interaction answer is **ephemeral** in Discord: it is scoped to the invoking user in the Discord UI. Its content is still disclosed to Discord and to the service operator; this is not end-to-end privacy. Cached command answers are prior evidence, not a fresh authorization check of their original resource. Every answer also sets `allowed_mentions: {parse: []}`, so output text can never ping anyone.

The line is passed as one argument (`SSH_ORIGINAL_COMMAND` becomes `--line "$SSH_ORIGINAL_COMMAND"`) with an otherwise empty environment. It never reaches a system shell. The Discord user chooses neither the workspace nor the home: both come from NAME by `render-authorized-keys.sh`'s rule. The sponsor gets `store/node/sponsor`; everyone else gets `sessions/NAME/workspace`.

The follow-up URL contains the interaction token, so it reaches `/usr/bin/curl` on stdin (`--config -`) and never argv. The body goes through a 0600 spool file, which is removed after the call.

## Making it live (DEPLOY)

Steps 1–4 happen on the workhorse. Step 5 is in `dregg-infra`, on the anchor. Step 6 is ember's.

1. **Binary.**
   - Build `native/discord-entrance` (`cargo +nightly-2026-06-21 build --release --locked`) the way the candidate's `mini` is built, so the glibc matches the workhorse (edge/README.md).
   - Install `target/release/mini-discord` as `/usr/local/lib/mini/mini-discord`, root:root 0755.
   - `mini-shell-ssh` is already at `/usr/local/lib/mini/` (deploy-1).
2. **Env.**
   - Copy `discord.env.example` to `/etc/mini/discord.env`, root:root **0600**.
   - Fill in `MINI_DISCORD_APPLICATION_ID` and `MINI_DISCORD_PUBLIC_KEY` from the Developer Portal (step 6).
   - `MINI_DISCORD_LISTEN=10.10.1.10:8793` keeps it off the public interface, which has no HTTP listener by design.
3. **Roster.**
   - Create `/etc/mini/discord-roster.json`, root:root 0644, in the shape of `discord-roster.example.json`.
   - Keys are Discord user ids. In Discord: Settings, Advanced, Developer Mode, then right-click the user and choose Copy User ID.
   - Values are session NAMEs from `edge/mini/friends/NAME.pub`.
   - A NAME's home must already exist. `render-authorized-keys.sh` makes it, so a friend is added to the ssh roster first, then here.
   - The file is re-read on every command, so no restart is needed.
4. **Unit.**
   - Create durable custody with `install -d -m 0700 -o mini -g mini /var/lib/mini/sessions/.discord-custody`. Keep this across service restarts and upgrades.
   - Install `mini-discord.service` to `/etc/systemd/system/`, then run `systemctl daemon-reload && systemctl enable --now mini-discord`.
   - It runs as `mini` in `mini.slice`.
   - Check it with `curl -s http://10.10.1.10:8793/healthz` from the anchor.
5. **Caddy** (anchor, `edge/anchor/Caddyfile` in `dregg-infra`). Add a site block, plus a DNS A/AAAA record for `discord.dregg.net` pointing at the anchor:

   ```caddy
   discord.dregg.net {
   	# Discord's interactions endpoint; everything else is 404 at the upstream.
   	reverse_proxy /interactions 10.10.1.10:8793
   	respond 404
   }
   ```

6. **Discord application (ember).**
   1. At <https://discord.com/developers/applications>, choose New Application. Copy the **Application ID** and the **Public Key** into step 2.
   2. Register the commands in the reviewed JSON catalog. The bot token is used here once, from ember's machine; it is never stored on the box:
      ```sh
      curl -X PUT -H "Authorization: Bot $TOKEN" -H 'Content-Type: application/json' \
        --data @deploy/discord/commands.json \
        https://discord.com/api/v10/applications/$APP_ID/commands
      ```
   3. In General Information, set **Interactions Endpoint URL** to `https://discord.dregg.net/interactions` and save. Discord sends a PING and a badly signed request, and saving succeeds only if they get PONG and 401.
   4. In Installation, add the app to a server with the `applications.commands` scope, or allow user install.

## Adding a friend

1. Add their ssh key: `edge/mini/friends/NAME.pub`, then `render-authorized-keys.sh`. This makes the session home.
2. Add `"<discord user id>": "NAME"` to `/etc/mini/discord-roster.json`.

A friend without an ssh key can still be given a session: create the home (`install -d -m 0700 -o mini -g mini /var/lib/mini/sessions/NAME`) and add the roster line. Their first lines are `/mini keygen mini.key` and then `/mini init mini.key SUBJECT` after enrollment, exactly as over ssh.

## The mirror runner (optional): one room <-> one channel

`mini-discord-mirror` bridges one chat room and one Discord channel, both ways. It is a **runner**, not part of the entrance:

- It holds its own session (its own key and workspace) and is a **member of the room**: the founder runs `chat invite ROOM SUBJECT bridge` for its subject and the bridge session runs the printed `chat join` line, like any friend. It has its own stream.
- **Room -> channel:** every poll is one `tail --in ROOM --json --discover @FILE -n 20` through the same forced command, a signed, metered Host read by the bridge's key. Each new `say` is posted to the channel webhook as `**name**: text` (`allowed_mentions` empty; `@` is broken with a zero-width space).
- **Channel -> room:** the channel's messages after the last one seen (`GET /channels/ID/messages`, the bot token). Each person's message becomes `say --in ROOM --via discord --via-id ID --via-name NAME --file F`: the **bridge** says it, signed by the bridge's key; the payload names the Discord author. It never signs as a friend. Readers see `bridge via discord NAME#ID: text`.
- **No loop:** an entry that carries `via`, or that the bridge's subject signed, is never posted up; a channel message with `webhook_id` (what the mirror posted) or from a bot is never said down.
- The environment is `MINI_MIRROR_ROOM`, `MINI_MIRROR_WEBHOOK_URL` and `MINI_MIRROR_BOT_TOKEN` (secrets: a 0600 EnvironmentFile), `MINI_MIRROR_CHANNEL_URL` (`https://discord.com/api/v10/channels/ID/messages`), `MINI_MIRROR_HOME`, `MINI_MIRROR_WORKSPACE`, `MINI_MIRROR_INTERVAL_S`, `MINI_MIRROR_PUBLISH_ROOM_TO_CHANNEL=yes`, `MINI_DISCORD_SPOOL`, plus the `MINI_SHELL_WRAPPER`... deployment variables above. The bot token travels to curl in its config on stdin, never argv.
- **ember's step:** a bot user in the application, invited to the server with Read Message History on that channel, and the **Message Content** privileged intent enabled (without it Discord returns empty `content` and nothing is said). This is a new secret on the box; the entrance itself still holds none.

### Durable room/channel custody

A mirror must explicitly set `MINI_MIRROR_PUBLISH_ROOM_TO_CHANNEL=yes`. This acknowledges an authorized disclosure mapping between the named Mini room and the configured Discord channel. Membership/read permission alone does not establish that every member consented to external publication. The interaction user's private answer and bridge publication are separate paths; `/mini-world` never posts its output into the channel.

The mirror keeps an owner-private `HOME/mirror` directory. A bridge lease binds its subject, room, workspace and channel URL; changing that mapping requires separate custody. Do not share one bridge home/room state between destinations. The room/channel identities and endpoint configuration are operator supplied; this runner does not prove the webhook points at the configured read channel.

- **Native → Discord:** `tail --discover @FILE --json -n 20` reads signed source pages using per-stream sequence cursors. At most 20 merged entries are examined each poll; each examined entry advances only its own stream cursor. New entries and skipped bridge/control entries cannot jump over an unprocessed older entry in that stream. Source `cell:sequence` is included in publications. Text exceeding Discord's limit is explicitly marked truncated; the full text remains at the Mini source. Incomplete/oversized/unreadable pages stop without moving cursors.
- **Discord → native:** one REST page (at most 50 records) per poll walks backward from a fixed channel head to the old watermark, retaining pages on disk. It then drains oldest-first, at most 20 records per poll. This avoids assuming how Discord selects an `after` page and never drops the oldest 30 of a 50-record page. A fresh bridge backfills available channel history; prior deletions and message edits are not a change-data feed. The initial retained source bytes are used for an interrupted delivery. Attachments are not imported; empty/bot/webhook records are passed over.
- Every inbound append uses `say --operation-record HOME/requests/discord-ROOM-MESSAGE.operation.json`. Mini retains its exact operation/attempt and recovers it; the mirror never makes a fresh proposal to replace an uncertain append. The Discord message ID remains in this operation filename, source text filename and retained page. The author in the Mini stream is the bridge; external author attribution stays in `via`.
- The outgoing operation record is synced **before** POST, and completion before its cursor. A crash after POST but before retained completion is **UNKNOWN**. It blocks this direction; it does not repost and does not claim exactly-once Discord delivery. The other direction can still make progress.
- After independently locating the destination message, an operator may stop the running mirror and run `mini-discord-mirror --resolve-up CELL SEQUENCE DISCORD_MESSAGE_ID` with the same environment. This records the operator's supplied evidence and sends nothing. It is an attestation, not an API verification. Restart then advances the retained source. An actually unsent uncertain post has no automated retry path yet.
- State and effect records use 0600 files, fsync-before-rename and directory fsync. Invalid JSON/state stops. Legacy height/message cursors are retained during migration; per-stream discovery scans the old prefix without republishing heights at or below the legacy height. This cannot repair gaps or duplicates produced by the old implementation. Make an operator-owned backup before upgrading; a legacy 0755 mirror directory must be made 0700.

The native source page currently covers each admitted member stream. Large rooms can exceed the entrance's 1 MiB capture limit; they fail closed rather than silently advancing. A future native total-byte/page budget is needed for such rooms. Custody is intentionally retained without an automatic garbage collector; disk-full errors stop new work.

### Local development and evidence

No command registration, real Discord messages or deployment is part of these tests.

```sh
cargo test --manifest-path native/discord-entrance/Cargo.toml --locked --offline --jobs 2
cargo build --manifest-path native/discord-entrance/Cargo.toml --bins --examples --locked --offline --jobs 2
```

Use the project's isolated target and resource guardian. The focused tests exercise signed HTTP interactions, persisted restart/UNKNOWN handling, actor-bound status, revocation, a 115-message backfill and a lost-publication reply. The mirror protocol tests use a stand-in forced command; they do not establish native Host admission.

`native/discord-entrance/tests/native-world.py` composes fake signed Discord, the actual entrance/wrapper/client, a fresh native Host/Store, an enrolled bridge and source-authorized room/document operations. Supply the exact pinned artifact manifest and a bootstrap helper with reviewed zero-tariff params. Its usage is in the script header. It requires a new private run directory and never imports a pre-existing world. Check `result.json` and the exact artifact pins; a passing historical ordinary profile does not qualify new language/private semantics or a deployment.

The old field-diff mode (`MINI_MIRROR_REF`, one cell's fields to a channel) is gone: it stood in for a stream until K-STREAM, and the room is the stream now. A unit configured with `MINI_MIRROR_REF` refuses to start (`MINI_MIRROR_ROOM is not set`).
