# The door: a stranger joins the demo box without the operator

`demo.dregg.online/join` is the one way a stranger gets a Mini account on the demo box. Before
the door, every friend needed ember by hand (a `friends/NAME.pub` commit, a roster render, the
friend's `keygen`, then `mini-reenroll NAME`), and pay-to-enrol landed on a proxy-mode row that
cannot sign (`docs/review/2026-10-26-deploy/HCLOUD-GAP.md` §3, §7 #9, #10, #18). The door does
those same steps, through the same scripts, on a timer. It requires split tenancy
(`/etc/mini/tenancy` = `split`) and refuses to run otherwise.

## Trust boundary

| who | uid | may write | may not |
|---|---|---|---|
| `mini-door` (the form, `native/discord-entrance/src/bin/mini-door.rs`) | `mini-door`, no groups | one bounded request file per POST in `/var/lib/mini-door/queue/` | reach any Mini socket, sudo, read any session; it holds no key and talks to no Store |
| `mini-discord` (the entrance) | `mini-discord` | one bounded link request per `/mini line:link CODE` in `/var/lib/mini-discord/door-links/` | write the Discord roster (it only reads it) |
| `mini-door-process` (the processor, `src/bin/mini-door-process.rs`) | root, oneshot every 60 s | the door's roster entries `$INFRA/friends/door/NAME.pub`, `/etc/mini/discord-roster.json`, its own state `/var/lib/mini-door-process/`, the status files the form shows | anything it was not asked for by a request of the exact schema |

- **The processor is the only writer** of door accounts, hosted keys, `authorized_keys` and the
  Discord roster. It reads a queue file only if it is a regular file (opened `O_NOFOLLOW`), owned
  by the queue's own uid, at most 8 KiB, and decodes to exactly one of the schemas in
  `src/door.rs` with no unknown key. Anything else is moved to `rejected/` with a reason and never
  acted on. The form's own checks are UX; the processor repeats every one of them.
- **It acts only through the box's existing scripts.** A door account is an operator-roster
  entry: the processor writes `NAME.pub` into the box's explicit per-box roster
  (`/usr/local/lib/mini/infra/friends/door/`, the installed `MINI_ROSTER_DIR`'s door subdirectory)
  and runs `render-authorized-keys.sh --on-box --roster $INFRA/friends`, which creates
  `mini-s-NAME`, its 0700 home and its key file. It then runs the session's own `keygen mini.key`
  as `mini-s-NAME` through `mini-shell-ssh` (the line the friend would have typed), and the
  existing `mini-reenroll NAME` with the door's fixed funding. There is no parallel enrolment path.
  The door subdirectory is the processor's: the Mac-side render's `rsync --delete` must not touch
  it (`infra/INSTALL.md` has the three-line change).
- **Every step is idempotent by request id** and the request's phase is retained before the next
  step starts. A crash anywhere is finished by the next tick; a refusal is final and shown.
- **The stranger's status page is a bearer URL.** The form issues a 128-bit request id; the
  processor writes `status/ID.json` (root:mini-door 0640) and the form shows it. It carries the
  login line, the Discord link code, and for a paid join the signing statement and the memo.

## Custody contract: who holds which key, for how long

| key | holder | where | for how long |
|---|---|---|---|
| the member's Mini signing key and its NEXT key | the member's own account `mini-s-NAME` | `sessions/NAME/keys/` (0700 home, 0600 files), made by the session's own `keygen` | the account's life; the box holds it by design (hosted), and the page says so |
| the member's ssh login key | the stranger | their machine; the box keeps only the public line | always |
| the sponsor's key | `mini-core` | the Store (`store/node/sponsor`) | the deployment |
| the enrollment receiving address | `mini-core` | `/var/lib/mini-core/secret/enrol.key` (0600), made fresh by `mini-enrol-keygen` at install | the deployment; ember imports `enrol-solana.json` to move what it receives |

**No other file ever holds a member key.** The processor itself only tests that `keys/mini.key` and
`keys/mini.key.pub` exist; it never opens either. Enrolment uses the possess flow: `mini-reenroll` (as patched in
`infra/dregg-infra.patch`) plans from the member's public key, copies the four public plan files into the
member's home, and the member's account signs the Host-chosen possession header there (`mini enroll
--action possess` as `mini-s-NAME`); the sponsor seals with the detached signature. The earlier flow
copied `keys/mini.key` into the sponsor's home (RUST-TRIAGE §4 row 1); that copy is gone. The paid route
never involves the sponsor. The proof is `jdoor.sh --box`: after enrolment it searches every file under
`/var/lib/mini`, `/etc/mini`, `/var/lib/mini-door*`, `/var/lib/mini-discord`, `/var/lib/mini-core` and
`/tmp` for the member's 32 key bytes and fails if any file outside `sessions/NAME/` contains them.

## Two routes, one processor

**Free** (`route=free`): the stranger gives a name and an ssh-ed25519 public key. The processor
creates the account, the hosted key and the login, then `mini-reenroll NAME` enrols the hosted key
from the sponsor's session and provisions it with the door's fixed `funding` (passed as
`MINI_REENROLL_FUNDING`). The page then says `ssh -t mini-s-NAME@demo.dregg.online`.

**Paid** (`route=paid`, P1): the same account, hosted key and login, but no sponsor funding.
The processor runs, as `mini-s-NAME`, `mini join --memo-version v2 --solana --key
HOME/keys/mini.key --ssh-public HOME/door/ssh.pub --dir HOME`: the box-held Mini key is the
enrolled identity and the stranger's ssh key is the login. Because the box never holds the
stranger's ssh secret, the memo's ssh possession is signed **detached**: the status page shows the
exact statement and one `ssh-keygen -Y sign -n dregg-enrol@v2` command; the stranger pastes the
signature back; the processor finishes the memo (`--ssh-signature`) and the page shows recipient,
amount, memo and the quote's expiry hour, and two ways to pay: **Pay with your wallet** (the page's
own one-shape serializer (`assets/solpay.js`, no SDK) and sol-misc's wallet adapter, `native/discord-entrance/assets/`; the
browser builds the TransferChecked from the stranger's associated token account to the recipient's
plus one Memo instruction with the exact memo bytes, the wallet signs, the browser sends it to the
public RPC `pay.rpc` names and posts the signature itself; the recipient's token account must exist,
the page never creates it) or pasting the transaction signature. Either way the stranger's transaction
signature reaches `/join/paid`; the processor runs `join --wait --signature TX`, which creates `HOME/workspace` from the
kernel's own enrolment (op 181). The receiving address is the deployment's fresh key (custody table
above), signed into the book by `mini pay book` and shown from the rendered pin; mainnet or devnet is
`pay.network` in `door.json`, and the RPC endpoints (Helius plus the public cluster endpoint, from the
box's `rpc.env`) follow the same switch (`deploy/pay/README.md`). The payment lands on a **hosted** account that signs on the box.
The enrollment view also lists the ssh key; `render-authorized-keys.sh` skips a view key equal to
an operator key, so the login stays the hosted line, never a proxy line.

**What the door supersedes.** For strangers on this box it replaces the operator's by-hand
onboarding (`deploy/shell/OPERATOR.md`, now operator-only) and the proxy-mode `mini join --solana`
v1 flow (`native/resource-client/src/join_solana.rs`, kept until the council rules on it). The v1
bootstrap routes `/mini/v1/*` stay served for existing pins; the door uses v2 over the public
socket.

## Funding and caps (`/etc/mini/door.json`)

- `funding`: the fixed provisioning of one free account (default `1000`, the amount
  `mini-reenroll` has always used).
- `freeCap`: the total number of free door accounts (default 50). `dailyCap`: free plus paid
  accounts created per UTC day (default 20). `perRun`: requests decided per tick (default 4).
- `inviteReserve` (default 0, which is a door without invite codes; at most `freeCap`, refused at load
  otherwise) and `inviteCodes` (an absolute path, required when `inviteReserve` > 0): of the `freeCap`
  seats, the last `inviteReserve` need an operator-issued invite code. An uncoded free request is
  admitted only while fewer than `freeCap - inviteReserve` free accounts exist (a coded member counts
  as a free account, so the reserve is never eaten by uncoded strangers); a coded one while fewer than
  `freeCap` exist. `dailyCap` and the form's per-/64 limits are unchanged. Refusals are named on the
  stranger's page: `open-seats-gone` (says how many remain for codes), `invite-unknown`, `invite-spent`.
  The join page then states the open and the reserved seats, and offers an optional code field; with
  `inviteReserve` 0 it mentions no codes.
- **The codes file** (`inviteCodes`; install it root:root, mode 0600; the processor refuses a symlink, a
  non-regular file, any group/other access, or a non-root owner). One code per line, `SERIAL CODE`: SERIAL
  a unique decimal of 1 or more, CODE a unique 8 to 64 of `A-Z a-z 0-9 -` (make them with
  `openssl rand -hex 16`); `#` comments and blank lines are kept. The processor strikes a code by rewriting
  the whole file atomically (temp, rename) to `SERIAL CODE used NAME REQUEST-ID AT`, BEFORE the
  request's first world effect; a crash then finds the request's own strike and carries on, never a second
  person. A request refused after its strike (the sponsor floor, at the funding step) returns the code.
  Add codes by appending lines (not while a tick runs: the processor holds its lock, so edit with
  `flock /var/lib/mini-door-process/.lock`). A coded member's world gets `invite` field 1 = the SERIAL
  (never the code; the world is world-readable) written as the member's own turns like `research-consent`;
  an uncoded member has no `invite` reference.
- `sponsorFloor`: before every free enrolment the processor reads the sponsor's balance with a
  signed `credit` read. Below `sponsorFloor + funding` the free route **closes**: the request is
  refused with `sponsorBelowFloor`, `door-state.json` says closed, and the form stops offering the
  free route. The paid route stays open (the stranger pays). Nothing fails silently: every refusal
  is a named reason on the stranger's page and a journal line.
- Mini's own per-member limits apply after enrolment (the sponsor's tariffs, the Host's lanes).
- `story` (optional; `{"author": "box", "name": "tale"}`, lowercase words): the built-in story every
  member joins, so the tour's story door has the member's own cell to move on. `author` is the account
  that holds the seed's `tale`, i.e. the seed's `SEED_HOST` (default `box`, which `door.json.example`
  carries; a node that runs the seed with `SEED_HOST=house` writes `"author": "house"`). After enrolment the
  author's account runs `story invite tale SUBJECT`, the processor hands the invitation to the member's
  `HOME/requests/tale-invite.json`, and the member runs `story join tale @tale-invite.json`: both are
  ordinary shell lines in each account's own session. Once per world: the world is named by the digest of
  the node's pinned config, so after a re-genesis (once the seed has made `tale` again) every member is
  invited again. The invitation is recorded before the join, so a failed join retries only the join. A
  failure is shown on the stranger's page (`story.error`) and never refuses enrolment; the next tick
  retries. Absent: no story step.

## Rate limits and abuse

- **Per IP**: nftables meters new connections on 443 (`edge/demo/host/nftables.conf`, the infra
  lane's); Caddy forwards `X-Real-IP`, and the form allows 3 new requests (`POST /join`) per IPv4 address or
  IPv6 /64 per hour (an in-memory table of 1,024 entries); a request's later steps (`/join/sign`,
  `/join/paid`) name a request already admitted and are not counted, so one stranger's paid route
  does not spend a shared address's hour. Only Caddy (loopback) is trusted for `X-Real-IP`.
- **Per queue**: the form refuses a POST while 32 requests are queued (503, "try later"). Bodies
  are at most 4 KiB, one request per connection, a 5 s read deadline, 16 concurrent connections.
- **Per key and name**: one account per ssh key (the processor refuses a key already in the
  roster) and names `^[a-z][a-z0-9-]{1,24}$`, never a reserved word
  (`ember`, `mini`, `core`, `keys`, `discord`, `door`, `root`, `admin`, `operator`, `sponsor`,
  `pubread`, `grain`, `web`) and never an existing account.
- **Discord**: a link code is 16 characters of base32 from the kernel CSPRNG, single-use, bound to
  one door account, valid 7 days; it can never map a Discord id to the sponsor or to an operator
  name, and a Discord id already on the roster is refused.
- **What a stranger gets is public**: everything on this box is world-readable to every member,
  and the account's key lives on the box (`website/join.html`). The page says so before the form.
- Retention: Discord custody and refusals are bounded (`deploy/discord/README.md`, "Retention").

## Composition with the box

- Split tenancy only. The processor reads the tenancy file and `lib.sh`'s layout; it runs the
  tenant's lines as `mini-session-run` does (`setpriv --reuid=mini-s-NAME --regid=mini-sessions
  --init-groups --reset-env`, a fixed environment, a timeout) and the sponsor's `credit` read as
  `mini-core`, exactly as `mini-reenroll` does.
- The Discord entrance runs a linked member's line through the root runner's socket
  (`/run/mini-session-run.sock`), not sudo, so it keeps `NoNewPrivileges=yes`
  (`deploy/discord/README.md`).
- `ship.sh --regenesis` re-runs `mini-reenroll --all`; door accounts are in the roster, so they are
  re-enrolled with everyone else.
- Removing a stranger: delete `$INFRA/friends/door/NAME.pub` and re-render; the account and home
  stay (their data), as for any friend.

## Phase 0 inputs this lane needs from ember

- the existing **Dragon's Egg** Discord application: its id and public key into the box's
  `/etc/mini/discord.env`, its Interactions Endpoint URL set to `https://demo.dregg.online/interactions`,
  and the `commands.json` PUT from ember's machine; the **room mirror** is off:
  it additionally needs a bot token with the Message Content intent, and `mini-discord-mirror`
  starts only with `MINI_MIRROR_PUBLISH_ROOM_TO_CHANNEL=yes`. The demo's Discord path is the
  entrance alone;
- mainnet or devnet for week 1 (`pay.network`; devnet also needs its mint); the Helius key
  (`~/.helius-key`, installed as the box's `rpc.env`); then, on the box, `mini-enrol-keygen`, the signed
  tariff with `enrolIndex` and `journalFloor` installed (`mini pay book`), and `enrol-v2.json` rendered
  with the fresh address;
- the door's numbers in `/etc/mini/door.json` if the defaults above are not right.

Files: `infra/` holds the units, the config, and `INSTALL.md` for the infra lane;
`native/resource-client/journey.d/jdoor.sh` is the journey.
