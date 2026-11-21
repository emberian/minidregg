# Installing the web front end on the demo box

For the infra lane. The design is `docs/WEB-FRONTEND-2026-10-27.md`; this is the box side, whole.
Three processes: the gateway `mini-web` (uid `mini-web`, loopback 8797, behind Caddy), the root
helper `mini-web-spawn` (one Unix socket, root:mini-web 0660), and per member a `mini web --body`
and `mini shell` the helper starts as `mini-s-NAME` in that member's `user-UID.slice`. The public
reader is one more hosted member, `public`, whose body the helper runs anonymously for every
visitor without a session. Nothing here needs `mini-pubread`, a render timer or `/srv/mini-public`:
those belonged to the deleted static snapshot.

## 1. Accounts and directories

```sh
useradd --system --user-group --home-dir /var/lib/mini-web --shell /usr/sbin/nologin mini-web
# mini-web is in NO other group: it reaches no Mini socket and no Store path.
install -d -m 0700 -o root -g root /var/lib/mini-web-spawn /var/lib/mini-web-spawn/logins /var/lib/mini-web-spawn/sessions
```

## 2. The public reader: the hosted member `public` (once per genesis)

The public reader is a real enrolled participant, made by the same roster → render → `keygen` →
`mini-reenroll` → `init` path every hosted friend takes (`deploy/shell/OPERATOR.md`, "An operator
friend"). Authors publish by delegating `observe` on a reference to its subject; the helper hands
the delegated references to its inbox; its body imports them and its own signed reads decide what a
visitor sees. The door refuses the name `public` to strangers.

1. **Roster entry.** The render needs one ssh-ed25519 line per roster file; the public reader has no
   human to log in, so its login key is a throwaway whose secret is destroyed at once:
   ```sh
   ssh-keygen -q -t ed25519 -N '' -C public -f /root/public-login
   cp /root/public-login.pub edge/demo/friends/public.pub      # in dregg-infra, commit it
   shred -u /root/public-login /root/public-login.pub            # nobody can ever log in as public
   BOX=dregg-demo MINI_ROSTER_DIR=edge/demo/friends edge/mini/render-authorized-keys.sh
   ```
   The render creates `mini-s-public`, its 0700 home `/var/lib/mini/sessions/public`, and an
   `authorized_keys.d` line nobody holds the key for.
2. **Its Mini key.** As the member, through the same forced command the door's processor uses
   (`mini-session-run`'s line; or a root shell): `setpriv --reuid=mini-s-public --regid=mini-sessions
   --init-groups --reset-env -- env -i PATH=/usr/bin:/bin LANG=C.UTF-8 SSH_ORIGINAL_COMMAND='keygen
   mini.key' /usr/local/lib/mini/mini-shell-ssh C/bin/mini C/bin/minidregg-host
   NODE/deployment/pinned-config.json NODE/public/mini.sock /var/lib/mini/sessions/public/workspace
   /var/lib/mini/sessions/public` (C = `/var/lib/mini/candidate/current`, NODE = `/var/lib/mini/store/node`).
3. **Enrol.** `/usr/local/lib/mini/mini-reenroll public` prints `public SUBJECT`. The public reader needs no
   funding beyond the default (it only reads); `MINI_REENROLL_FUNDING=0` is fine if the sponsor's
   floor is close.
4. **Init** its workspace with that subject (the same forced-command line with `SSH_ORIGINAL_COMMAND='init
   mini.key SUBJECT'`), and **record the subject for the box**:
   ```sh
   printf '%s\n' SUBJECT > /etc/mini/public-subject && chmod 0644 /etc/mini/public-subject
   ```
   The helper passes it to every body (`--public-subject`): members see "Publish to the public
   reader" on their document pages, and the hand-off sweep knows whom to deliver to. Without the
   file the front end runs, but no document can be published and the public reader shows only what
   it was given by hand.
5. `ship.sh --regenesis` re-enrols `public` with everyone else (`mini-reenroll --all`); after a
   re-genesis repeat step 4 with the new subject.

## 3. Binaries

From the candidate: `mini-web` and `mini-web-spawn` are workspace members
(`cargo build --release -p minidregg-mini-web -p minidregg-mini-web-spawn`), installed as
`/usr/local/bin/mini-web` and `/usr/local/bin/mini-web-spawn` (root 0755). The body is the
candidate's own `mini` (`mini web --body`), started by the helper as the member with the same
paths `mini-shell-ssh` receives.

## 4. Units

```sh
install -m 0644 deploy/web-frontend/mini-web.service deploy/web-frontend/mini-web-spawn.socket deploy/web-frontend/mini-web-spawn.service /etc/systemd/system/
install -d /etc/systemd/system/mini-web.service.d /etc/systemd/system/mini-web-spawn.service.d
install -m 0644 deploy/web-frontend/demo/mini-web.service.d-60-demo-confine.conf /etc/systemd/system/mini-web.service.d/60-demo-confine.conf
install -m 0644 deploy/web-frontend/demo/mini-web-spawn.service.d-60-demo-confine.conf /etc/systemd/system/mini-web-spawn.service.d/60-demo-confine.conf
printf 'MINI_WEB_ORIGIN=https://demo.dregg.online\nMINI_WEB_SHUTDOWN=11 November 2026\nMINI_WEB_FRAME_SRC=\n' >/etc/mini/web.env
systemctl daemon-reload
systemctl enable --now mini-web-spawn.socket mini-web-spawn.service mini-web.service
```

The unit passes `--registry /var/lib/mini/candidate/current/protocol/host-operations.json`: the public
`/registry` page renders the operation registry (bytes, receivers, effects, markers, consent plans)
from the candidate's own file, read-only. `MINI_WEB_FRAME_SRC` is the CSP `frame-src` for grains
opened in a pane (L13's per-grain origins, e.g. `https://*.demo.dregg.online`); empty means `'none'`.

**The public front page's document** is one name in `/etc/mini/front-doc` (the demo seed's
`welcome`: `printf 'welcome\n' >/etc/mini/front-doc`). `mini-web-spawn` reads it, like
`/etc/mini/public-subject`, and passes `--front-doc NAME` to the public reader's body only. `/` then
renders that published document through the ordinary page path, with a link to `/doc`, the index
of everything published. If the file is absent, empty or not a reference name (`[A-Za-z0-9-]`, at
most 64), or the document is not published to the public reader, `/` is the index as before.
Members' front pages are unchanged.

**Whose publication a house name is** is `/etc/mini/house-publications`, root-owned, one
`NAME MEMBER` per line: the demo's `welcome house` and, once the box member exists,
`operations box` (`printf 'welcome house\n' >/etc/mini/house-publications`). The front page's
document, `operations` and every name listed are house names: the helper hands a publication over
under a house name only from the member listed for it, and anyone else's document of that name as
`NAME-MEMBER`, so no member's page can become the front page or the box's operations room by
taking the name first. Without the file every house name is nobody's, and `/` is the index.

**What the helper does on its own**, besides spawning: every 60 s it sweeps every member home's
`workspace/proposals/*/recipient-reference.json` for references addressed to the public subject and
copies each into `/var/lib/mini/sessions/public/inbox/NAME.TARGET.json` (owned by `mini-s-public`,
0600); it decides nothing. The public body imports new inbox files before it renders its index
(`mini workspace --action import --from-ref`); a name already taken gets `NAME-CAPABILITY`. A
revoked grant renders nothing: the signed read refuses.

**It warms the public reader.** At its start and at every sweep, when `/etc/mini/public-subject`
exists and no live public body answers from the current basis (subject, front document, the
reader's `workspace.json`, the pinned config, the candidate), it starts the public body and sends it
one `GET /`, so the body's start and its consent worker's Store replay are paid before the first
visitor (demo-dry 2026-10-28: 23 s cold on an idle box, the gateway's 504 at 120 s under load). The
journal says `public reader warmed (body PID): HTTP/1.1 200 OK in N s`. A body whose basis changed (a
re-genesis, a re-enrolled reader, a new front document) is ended and replaced. Keeping the worker
warm afterwards is the frame's: `mini-consent@public` does not idle out (dregg-infra, install.sh).
The tour's J-COLD-READ rows (`journey.d/jweb-frontend.sh`) check the cold path.

The `install-demo.sh` contract check: `mini-web.service` carries the full
`placeholders/web-gateway.conf` floor; `mini-web-spawn.service` is root by design (the door's
`mini-session-run@.service` is its precedent) and declares its `CapabilityBoundingSet`,
`ProtectSystem=strict` and exact `ReadWritePaths` (the member homes, for the hand-off).

## 5. Caddy

Import `deploy/web-frontend/Caddyfile.app` into the `demo.dregg.online` block after the `/join`,
`/interactions` and `/mini/v1/*` handles, in place of the fallback `handle` and any docuverse
snapshot route. `/ws/*` is the terminal's WebSocket; the second handle is everything else.

## 6. The door

The door's files on this branch carry two changes: the processor writes the one-time web login
record when it enrols an account (`native/discord-entrance/src/bin/mini-door-process.rs`,
`enrolled()`: `/var/lib/mini-web-spawn/logins/<sha256(code)>.json` = `{name, request, expires}`,
root 0600) and publishes `webLogin` (`https://HOST/login/CODE`) on the stranger's status page beside
the ssh line; and `public` joined the reserved names. The code lives `linkTtlHours` (7 days by
default). The processor remains the only writer of identities.

## 7. What "publish" means for a member

On a document page the member presses **Publish to the public reader**: the body runs
`delegate ID DOC PUBLIC-SUBJECT observe MAX` (MAX from `deploy/demo-seed/public-read-request-bytes`, the cost ceiling of one read; 0 covers no read and every visitor is refused `no-grant`), `submit ID`, `publish ID` as the member (the same
three lines the shell takes; `/verb/delegate` is the general form). The helper's sweep delivers
the reference within a minute; the public reader imports it at its next render; every visitor then
reads the document as the public reader does, under the author's grant. **Unpublish** runs
`revoke ID DOC PUBLIC-SUBJECT` and `submit ID`; the page refuses at the next signed read. Links out
of a published document show their target ids; a published room shows its members.

## 8. Check

```sh
systemctl is-active mini-web-spawn.socket mini-web-spawn.service mini-web.service
curl -s http://127.0.0.1:8797/healthz                                  # ok
ls -la /run/mini-web-spawn.sock                                        # srw-rw---- root mini-web
sudo -u mini-web ls /var/lib/mini/store 2>&1 | grep -q denied && echo "gateway cannot see the Store"
curl -s http://127.0.0.1:8797/ | grep -c 'public reader'               # the anonymous body answers
native/resource-client/journey.d/jweb-frontend.sh --box NAME           # as root; NAME a hosted account
```

The journey writes a login record as the door would, opens a session through the gateway with the
public Origin, runs `whoami` in a terminal over the WebSocket, creates and appends a document through
the forms, reads the receipt, checks every shell leaf has a form that plans (`parity`), logs out, and
checks the public reader answers `/`.

## 9. What an RCE reaches

Gateway: the session ids of requests in flight (so those members' bodies and shells while the
sessions live), `/var/lib/mini-web`, nothing else; no key, no Store, no network. Helper: root; it is
the only such process and refuses everything but its seven verbs from uid `mini-web`; its sweep
only copies files it has parsed as delegated references. Body or shell: that member's key and the
world-readable Store, as the ssh shell does; the public body holds the public reader's key, which
holds only observe grants.
