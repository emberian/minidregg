# Installing the door on the demo box (for the infra lane)

Everything here belongs in `~/dev/dregg-infra` (branch `demo-vm`); this lane wrote it but does not edit
that repo. The design is `deploy/door/README.md`. Split tenancy is required.

## 1. Apply the patch

```sh
cd ~/dev/dregg-infra   # branch demo-vm
git apply --check ~/dev/minidregg/deploy/door/infra/dregg-infra.patch && git apply ~/dev/minidregg/deploy/door/infra/dregg-infra.patch
```

It was made against `demo-vm` at `434aeb6` and checks clean there. What it changes:

| file | change | why |
|---|---|---|
| `edge/mini/render-authorized-keys.sh` | reads `friends/door/*.pub` (hosted only, an operator name refuses a colliding door name); the Mac half's rsync gains `--exclude=/door/`; defines `TENANT_GROUP`/`HOSTED_GROUP` | door logins live in the box's own per-box roster, and an operator render must never delete them. The `--on-box` half never sourced `lib.sh`, so creating a hosted account died on an unset `$TENANT_GROUP` under `set -u`: an existing defect the door is the first to exercise |
| `edge/mini/mini-reenroll` | **custody**: plans from the member's PUBLIC key, hands the four public plan files to the member's account, which signs possession there (`mini enroll --action possess` as `mini-s-NAME`), then seals with that detached signature; `MINI_REENROLL_FUNDING` (default 1000); finds `friends/door/NAME.pub`; `--all` includes door entries | the old flow copied `keys/mini.key` into the sponsor's home before enrolling (RUST-TRIAGE §4 row 1). Now no file outside the member's 0700 home ever holds the key |
| `edge/mini/install.sh` | creates `mini-door` (no groups) and the door's directories; refuses members in group `mini-discord`; removes the `mini-session-run` sudoers rule; the Discord drop-in no longer lifts `NoNewPrivileges` and sets `MINI_SESSION_RUNNER=/run/mini-session-run.sock`, `ReadWritePaths=/var/lib/mini-discord` only; installs the five new units | the runner is a socket now; the entrance keeps its hardening |
| `edge/mini/mini-components` | `door`/`door-process` on with split tenancy, both binaries and `/etc/mini/door.json`; `session-run` socket on with split tenancy and the Discord entrance | |
| `edge/demo/host/caddy/Caddyfile` | `handle /join*` → `127.0.0.1:8796` with `X-Real-IP` and a 4 KB body cap; the root answer names `/join` | |

## 2. Copy the files

| from `deploy/door/infra/` | to dregg-infra | note |
|---|---|---|
| `mini-session-run` | `edge/mini/mini-session-run` (replaces it) | socket protocol, no `SUDO_USER` |
| `mini-session-run.socket`, `mini-session-run@.service` | `edge/mini/` | root:mini-discord 0660, `Accept=yes` |
| `mini-door.service`, `mini-door-process.service`, `mini-door-process.timer` | `edge/mini/` | binaries from the candidate (`bin/mini-door`, `bin/mini-door-process`, packaged as roles `door`, `doorProcess`) |
| `mini-enrol-keygen` | `edge/mini/`, and add it to `SCRIPTS` in `install.sh` | run once per deployment (step 3) |
| `demo/<unit>.d-60-demo-confine.conf` | `edge/demo/host/systemd/<unit>.d/60-demo-confine.conf` | none of the three units is in an egress set; a member's Discord line now runs in the runner's cgroup and so has no egress at all (under sudo it inherited `cg_discord`) |
| `door.json.example` | `/etc/mini/door.json` on the box (root 0644) | the numbers in `deploy/door/README.md`; `pay` is `null` until PAY is set up |

## 3. Secrets and parameters (never in git)

- **Invite codes.** `door.json.example` carries `"inviteReserve": 20` (of `freeCap` 50) and
  `"inviteCodes": "/etc/mini/invite-codes"`. Install the codes file `/etc/mini/invite-codes` as
  `install -o root -g root -m 0600`, one `SERIAL CODE` line per code (serial a unique decimal of 1 or
  more; code 8 to 64 of `A-Z a-z 0-9 -`, e.g. `openssl rand -hex 16`); see `deploy/door/README.md`.
  The processor refuses to read it if it is not root-owned mode 0600, and a missing file stops coded
  requests (named in their status) while uncoded ones go on. Never commit it.
- **Solana RPC (Helius).** ember's key is `~/.helius-key` on the Mac. Install
  `/etc/mini/pay/rpc.env` (root 0600) on the box with
  `PAY_RPC_ENDPOINTS=https://mainnet.helius-rpc.com/?api-key=KEY https://api.mainnet-beta.solana.com`
  for mainnet, or the `devnet.helius-rpc.com` / `api.devnet.solana.com` pair for devnet
  (`deploy/pay/README.md` step 4). The two must match the `pay.network` in `door.json` and the
  `--network` given to `render-enrol`.
- **The enrollment address.** On the box, once: `mini-enrol-keygen` prints the fresh address and keeps the
  seed in `/var/lib/mini-core/secret/` (mini-core 0600). Then `render-enrol --enrol-address-file
  /var/lib/mini-core/secret/enrol.pub --network mainnet|devnet [...]` and the three `mini pay book` /
  `mini pay address` steps of `deploy/pay/README.md`; install the rendered `enrol-v2.json` as
  `/etc/mini/pay/enrol-v2.json` (the door's `pay.enrolPin`) and `watcher.env`.
- **Discord: the existing "Dragon's Egg" application.** Its application id and public key go into
  `/etc/mini/discord.env` (root 0600; `deploy/discord/discord.env.example`, with
  `MINI_DISCORD_DOOR_URL=https://demo.dregg.online/join`). Its Interactions Endpoint URL must be set to
  `https://demo.dregg.online/interactions`. The bot token stays where it is: the entrance never reads it;
  only the command registration (from ember's machine) and the off-by-default room mirror (through
  `mini-keys`) use it.

## 4. Check

```sh
systemctl status mini-door mini-door-process.timer mini-session-run.socket
curl -s http://127.0.0.1:8796/healthz                  # ok
/var/lib/mini/candidate/current/bin/mini-door-process  # one pass by hand; it writes door-state.json
cat /var/lib/mini-door-status/door-state.json
MINI_ROOT= bash ~/minidregg/native/resource-client/journey.d/jdoor.sh --box   # the box journey (root)
```

`jdoor.sh --box` signs up a test stranger through the form, runs the processor, logs in over ssh as
`mini-s-NAME`, makes one write, and checks that no file outside the member's home holds the member's key.
