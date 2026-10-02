# Discord entrance

`mini-discord` lets a friend use Mini from Discord. It adds no new verbs:

- A Discord user maps to one Mini session through the roster, and the session's key is held on the box, as it is for the ssh entrance.
- `/mini <line>` hands the line to `mini shell --line`, through the same forced command (`deploy/shell/mini-shell-ssh`) that ssh uses.
- `/mini-help` runs the shell's own `help`.

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
   - An interaction id seen in the last 15 minutes is refused with 401 `replayed interaction`.
2. **PING.** It gets PONG.
3. **Roster.**
   - The roster file must be owned by root and must not be writable by group or others. A file that fails any check answers no one.
   - A Discord user who is not on the roster gets, at once:
     `error: Discord user <id> is not on this Mini's roster; nothing ran. Ember must add you: send ember this id.`
4. **Line.**
   - The line must be at most 1000 characters and a single line. Otherwise the answer is `usage: …`, sent at once and logged.
   - At most 4 lines run at a time across sessions.
   - Lines of one session run one at a time, in order.
5. **Deferred answer.**
   - The entrance answers `DEFERRED` (type 5, ephemeral) within milliseconds.
   - Only after that answer is written does it run the line. A turn takes 2–7 s, and Discord allows 3 s for the first answer.
   - It then PATCHes `@original` with one of two things:
     - the shell's stdout in a code block, cut to 2000 characters with a note saying how much was shown;
     - on failure, the shell's own ending line verbatim (`error:` / `usage:` / `refused:` / `undecided:`).
6. **Log.**
   - `(user, line, ending, exit)` is appended to `SESSIONS/NAME/discord.log` (0600).
   - The entrance's journal records user, session and ending. It never records the interaction token.

Every answer is **ephemeral**: only the invoking user sees their session's output. Every answer also sets `allowed_mentions: {parse: []}`, so output text can never ping anyone.

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
   2. Register the two commands. The bot token is used here once, from ember's machine; it is never stored on the box:
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
- **Room -> channel:** every poll is one `tail --in ROOM --json --since H` through the same forced command, a signed, metered Host read by the bridge's key. Each new `say` is posted to the channel webhook as `**name**: text` (`allowed_mentions` empty; `@` is broken with a zero-width space).
- **Channel -> room:** the channel's messages after the last one seen (`GET /channels/ID/messages`, the bot token). Each person's message becomes `say --in ROOM --via discord --via-id ID --via-name NAME --file F`: the **bridge** says it, signed by the bridge's key; the payload names the Discord author. It never signs as a friend. Readers see `bridge via discord NAME#ID: text`.
- **No loop:** an entry that carries `via`, or that the bridge's subject signed, is never posted up; a channel message with `webhook_id` (what the mirror posted) or from a bot is never said down.
- The environment is `MINI_MIRROR_ROOM`, `MINI_MIRROR_WEBHOOK_URL` and `MINI_MIRROR_BOT_TOKEN` (secrets: a 0600 EnvironmentFile), `MINI_MIRROR_CHANNEL_URL` (`https://discord.com/api/v10/channels/ID/messages`), `MINI_MIRROR_HOME`, `MINI_MIRROR_WORKSPACE`, `MINI_MIRROR_INTERVAL_S`, `MINI_DISCORD_SPOOL`, plus the `MINI_SHELL_WRAPPER`... deployment variables above. The bot token travels to curl in its config on stdin, never argv.
- **ember's step:** a bot user in the application, invited to the server with Read Message History on that channel, and the **Message Content** privileged intent enabled (without it Discord returns empty `content` and nothing is said). This is a new secret on the box; the entrance itself still holds none.

The old field-diff mode (`MINI_MIRROR_REF`, one cell's fields to a channel) is gone: it stood in for a stream until K-STREAM, and the room is the stream now. A unit configured with `MINI_MIRROR_REF` refuses to start (`MINI_MIRROR_ROOM is not set`).
