# The Mini web front end

Present-state design, 2026-10-27. One application, one design language, one front end: a member's
browser session **is their world**. Ember's bar: "at minimum some high quality lightweight embedded
terminal plus nice reasonably minimal html forms for dealing with the rest of it", raised the same
night to "design the Mini web experience whole". Everything older (the loopback `mini web` with a
path secret, the `--read-only` face, the `--render-static` snapshot, `deploy/web`'s pubread timer)
is compost: its document rendering, shared-name link handling and escape hygiene move into the one
front end; the rest is deleted in this series. There is no degraded mode and no "week 1".

## 1. What a person sees

`https://demo.dregg.online/` is the application. Without a session it shows the world as the
`public` subject may observe it (what members chose to publish) and one door: **Join** (the
self-serve door at `/join`) / **Open your session** (the one-time link the door issued). With a
session it is the member's workspace. One HTML page shell for both: a top bar (Mini · the subject ·
search · Log out), a rail of places, and the stage.

| place | route | what it holds | the verbs behind it |
|---|---|---|---|
| Documents | `/doc`, `/doc/N`, `/doc/N/history`, `/doc/N/diff/A/B`, `/at/H/doc/N`, `/doc/N/edit`, `/new-document` | the list, a page (element-tree order, transclusions inline, links and backlinks), history, a page at a height, a diff, append/edit, create | signed reads (`workspace::signed_view`, `rendered_document`), the editor's pinned diff + durable attempt, `doc append`, `doc link` |
| Boards | `/board/N` | columns and tasks; add / move / take | `board add|move|take` |
| Rooms | `/room/N` | members, the room's streams as chat, say; the index; a resident's turns | `room ls`, `say`, `tail`, `room members`, `summon` |
| Apps | `/apps[?q=]`, `/apps/APP`, `/grain`, `/grain/N`, `/grain/N/pane` | the Sandstorm app market (`apps search --json`: the publisher's claims beside the box's verdict), one entry, install; the member's grains, a grain's state / routes / held identities with open, start, stop, share, export, delete, revoke-identity; the one-time bootstrap posted to the grain's own origin, then the grain in a pane | `apps search|show|install|list|status|open|share|…` (L13, `docs/APP-MARKET-2026-10-27.md` §5a) |
| Residents | `/room/N/resident` | summon a Hermes resident into a room; its turns as they land | `summon`, `tail` |
| Receipts | `/receipts`, `/receipts/ID` | the newest 50 retained attempts with their decoded outcome: **admitted** / **refused** with the clause / **undecided** with the exact retry; `why`; `lookup`; `retry` | `history all`, `inspect receipt`, `why`, `lookup`, `retry` |
| Grants & laws | `/grants`, `/laws` | what my grants cover (`can`), delegate, revoke; the law on a reference, install a law | `can`, `delegate`, `revoke`, `inspect law`, `law` |
| Keys & sessions | `/keys`, `/sessions` | the hosted-custody statement (the key lives on the box, world-readable world), key status and rotation; this account's web sessions, revoke any | `whoami`, `key-status`, `rotate-key`; the helper's session list |
| Purse | `/purse` | the account as a meter (`credit`), pay status, top up, tariffs | `credit`, `pay status`, `topup`, `tariff` |
| Commands | `/verb`, `/verb/NAME` | **every shell verb as a form, derived from the shell's verb table** (`shell::command_catalog`: shell, chat, hermes, story): one form per usage alternative, reference arguments as pickers over the workspace's refs, text through `@FILE`, a fresh proposal id with "and `submit ID`"; the answer is the one outcome partial | all of them |
| Terminal | `/term` | `mini shell` as this member, in the page (a convenience, never the parity mechanism) | the shell itself |
| Tour | `/tour`, `/tour/N` | the twelve steps of `docs/DEMO-EXPERIENCE-2026-10-27.md` §1 as one page whose forms are the real derived forms; a step's outcome lands under it | the steps' verbs |
| Registry | `/registry` | the operation registry (bytes, receivers, effects, markers, consent plans) and the Lean-emitted default laws, for every visitor | data files of the candidate |
| the front page (public) | `/` | what the public reader may observe: published documents, the operations room (`operations`, posted into by `mini-s-box`; named when absent), the receipts stream newest first, the laws | the public body |

**Parity** (ember 2026-10-27, `docs/DEMO-EXPERIENCE-2026-10-27.md` §1a): everything the shell can do,
the browser can do, visually. The derived forms (`web/verbs.rs`) are the mechanism: a new verb is
visual the day its row enters the table; the journey's `parity` row checks every verb × subcommand leaf
`help` lists against `/verb/NAME`'s forms and names any without a face (and red-proofs itself on a
verb the shell lacks); it is coverage, not parity, until every leaf also has an outcome test. The
usage-derived forms are the interim; the structured command grammar (A0) replaces them verb by verb.
Outcome truth: admitted / refused / undecided name world transitions only; a read or a local verb
answers (`answered`, `read refused`), classified per usage alternative from the verb table. Bespoke views sit where a place deserves
one: the document page, history and diff pages, the board, the room as a live stream (the chat
section refreshes), the receipt, the grants drawn as a tree from the Host's capability view, the
purse as a meter, and a refusal as its clause highlighted.

**Forms work without JavaScript**: every route is a whole page; every action is a `<form method=post>`
whose answer is the decoded outcome rendered by one partial (`outcome`), with the next step as a link
(`retry` for undecided, `why` for refused, the receipt for admitted). **With JavaScript** (one file,
`app.js`, ~400 lines, no framework) the same links open as **panes** on the stage: the server answers a
request carrying `X-Mini-Fragment: 1` with the stage region only; panes tile and overlap, have a title
bar, close, maximize, and their set is kept in the URL hash so reload restores a workspace. The
Terminal pane is xterm.js (`@xterm/xterm` 5.5.0 + `addon-fit` 0.10.0, vendored under
`native/mini-web/assets/vendor/`, pinned by sha256; no CDN; the box has no egress and the page loads
no third-party script). Copy/paste, resize, mobile keyboard, reconnect to a live shell.

**One design language**: the gateway, direct reader and join door share `app.css`; warm paper,
forest accent, system sans for controls and serif for reading, light and dark tokens, responsive
cards and grammar-derived field groups. The public front composes the existing welcome document,
operations read and app catalogue; the market renders the catalogue as cards. Refusals retain their
clauses and next steps. Details and before/after previews: `docs/WEB-DESIGN-2026-10-28.md`.
The world-readable sentence (D8) remains in the gateway footer for every visitor.

## 2. The mechanism: sshd's privilege separation, for the browser

```
browser ──443──▶ Caddy ──loopback 8797──▶ mini-web (uid mini-web: NO key, NO Store, NO socket paths)
                                             │ one Unix socket, 0660 root:mini-web, SO_PEERCRED-checked
                                             ▼
                                    mini-web-spawn (root; tiny; synchronous; the ONLY privilege)
                                       ├─ login CODE          → session (the door wrote CODE)
                                       ├─ shell SID COLS ROWS → pty master fd  (mini shell as mini-s-NAME)
                                       ├─ body SID            → connected fd   (mini web as mini-s-NAME)
                                       ├─ body public         → connected fd   (mini web as mini-pubread)
                                       └─ logout / sessions / revoke
```

- **The gateway** (`native/mini-web`, binary `mini-web`) serves HTTP/1.1 on loopback with the same
  hand-rolled, bounded style as `mini web` and `mini-door` (16 KiB head, 192 KiB body, 10 s ingress,
  a pool, `Connection: close`); the tree has no HTTP framework and this adds none. It holds the page
  shell, the assets, and cookies. It never sees a key, a Store path or a socket path: everything it
  knows about a member it learns from the helper, by an opaque session id.
- **The helper** (`native/mini-web-spawn`, root) is the analogue of the door's `mini-session-run`,
  with a pty and fd passing instead of a captured line. One request per connection, one line in,
  one line out, an fd by `SCM_RIGHTS` when the answer is a shell or a body. It refuses any peer whose
  uid is not `mini-web`, any malformed line, any name that is not a hosted account in
  `mini-hosted` with its 0700 home, and any session it did not itself create. It spawns through the
  **same line** `mini-session-run` uses (`setpriv --reuid=mini-s-NAME --regid=mini-sessions
  --init-groups --reset-env -- env -i PATH=/usr/bin:/bin LANG=C.UTF-8 … mini-shell-ssh MINI HOST
  CONFIG SOCKET WORKSPACE HOME`), inside `systemd-run --scope --slice=user-UID.slice` with the
  member's quotas, so ssh and web sessions share one cap (`user-mini.slice.conf`, 1G per tenant;
  the demo's `user.slice` 8G). The pty's lifetime is the shell's: when the gateway drops the master
  (or revokes the session) the shell gets SIGHUP.
- **The body** is `mini web --body`: the compost of today's `web.rs`, grown into the member's
  rendering process. It listens on the inherited fd 3 (a Unix listener the helper bound under
  `/run/mini-web-spawn/bodies/`, a root-only directory, so no uid but root can connect to any body)
  and answers fragment requests: GET renders (the `Site` methods, links under `/`), POST actions that
  run `shell::line` with the verb the form names and render the `(exit, text)` ending as the outcome
  partial (exit 3 = refused, 4 = undecided, 0 = admitted; the text is the classifier's, never the
  reply byte's). The public body runs as `mini-pubread` over the `public` workspace with
  `--anonymous`: no write affordance, every POST refused before any read.
- **Sessions.** The door's root processor, when it enrols an account, writes
  `/var/lib/mini-web-spawn/logins/<sha256(code)>.json` (`{name, expires}`, root 0600) and shows
  `https://demo.dregg.online/login/CODE` on the stranger's status page beside the ssh line. The
  gateway shows a confirm form (so a link preview never burns the code); the POST sends `login CODE`
  to the helper, which deletes the record and mints a session: 32 random bytes, stored by sha256
  under `sessions/`, with the name, a CSRF secret, created / last-seen / expires (idle 24 h, hard
  7 d). The cookie is `__Host-mini_session`, `Secure; HttpOnly; SameSite=Strict; Path=/`; it names a
  session, never a key. Every POST carries the session's CSRF token (the gateway adds the hidden field to every
  POST form on the page it serves, the body's forms included, so the token never reaches the body)
  and must arrive with `Sec-Fetch-Site: same-origin` (or none) and an `Origin` equal to the public
  origin; the WebSocket upgrade checks `Origin` the same way. `/sessions` lists this account's sessions and revokes any;
  logout revokes the current one and ends its body and shells.
- **Terminal transport.** `/ws/term/ID`: RFC 6455 server side in the gateway (SHA-1 via `ring`, which
  the workspace already links); binary frames carry pty bytes both ways, one text frame
  `{"resize":[cols,rows]}` sets the window size (`TIOCSWINSZ`); the gateway keeps a 64 KiB replay
  ring per terminal and holds the pty 60 s after a socket drops, so a reload or a flaky network
  rejoins the same shell. N shells per session, bounded (8).

**What an RCE reaches** (stated honestly, CONFINEMENT §6 style): in the gateway, the session ids of
requests it is serving, so those members' bodies and shells while the sessions live, and nothing on
disk but its own state directory; no key, no Store, no socket path, no network. In the helper: root,
by construction the only such process; it is ~600 lines, synchronous, and refuses everything but the
six verbs from one uid. In a body or shell: that member's key and the world-readable Store, exactly
what the ssh shell reaches. Nothing listens on a public port except through Caddy.

## 3. What is reused, what is deleted

Reused: `web.rs`'s `Site` renders (document, history, diff, board, room, inspect, search, resident),
`editor.rs`/`create.rs` (pinned diff, durable attempt), the shared-name link repair and the
escape hygiene L7 landed, `web_admission.rs`'s pool (now over TCP and Unix streams), `parse_request`,
`mini shell` in script mode and its classifier, the door's `mini-session-run` spawn line and its
refusals, the demo drop-in floor (`host/systemd/placeholders/web-gateway.conf`). Deleted in this
series (commit "compost"): `--read-only` and its gate branches, `--public-origin`, `--render-static`,
`render_static`/`write_snapshot`, `Face::Static`, `STATIC_HISTORY_PAGES`, `SNAPSHOT_NOTE`, their
tests, `deploy/web/` (pubread timer, collect scripts, `Caddyfile.docuverse`), jweb's `ro-*` and
`static-*` rows, and the join page's "static snapshot" sentences. Kept: the loopback TCP face with its
per-launch secret, as the developer's and the journeys' direct face over the same `Site` (jweb,
jdocuverse J24 drive the renders through it; it is one renderer behind two transports, not a twin).
Studio stays routed nowhere in the body (its deletion is L2's, D7).

## 4. Files

| path | what |
|---|---|
| `native/mini-web/` | the gateway: `main.rs` (listener, pool, router), `http.rs`, `session.rs` (cookie, CSRF, helper client), `ws.rs` (RFC 6455), `term.rs` (pty bridge, replay ring), `proxy.rs` (the body over the helper's fd), `page.rs` (the page shell and partials), `assets/` (`app.css`, `app.js`, `vendor/xterm*` pinned in `VENDOR.md`); `native/mini-web/tests/dev_flow.rs` runs the real helper (`--dev`) and gateway end to end without a Host |
| `native/mini-web-spawn/` | the helper: `main.rs` (socket loop, peer check, verbs), `spawn.rs` (pty, setpriv line, scope), `store.rs` (logins, sessions) |
| `native/resource-client/src/web.rs` + `web/` | the body face |
| `deploy/web-frontend/` | `mini-web.service`, `mini-web-spawn.{socket,service}`, the 60-demo-confine drop-ins against the demo floor, `Caddyfile.app`, `door.patch`, `INSTALL.md` |
| `native/resource-client/journey.d/jweb-frontend.sh` (+ `jweb-frontend-ws.py`) | the JWF step after WEB: login code → cookie → terminal `whoami` over the WebSocket → `doc new` and append through the forms → receipt admitted → logout revokes → public reader; as a journey hook, `--dry` from the environment, `--box NAME` on the box |

## 5. Seams owned elsewhere

L13's `apps` verb (lane/app-market 1c7a7f30) is the market: `web/apps.rs` runs it as the member and
draws its `--json` replies; `MINI_WEB_FRAME_SRC` names the grain origins for the pane; the
`identityNotice` on its receipts is shown on the receipt and the Grants page. L5 owns
the door; the patch in `deploy/web-frontend/door.patch` adds the login record and the one status
line. The infra lane installs `deploy/web-frontend/INSTALL.md` and retargets Caddy's `handle` to the
gateway (the fallback `handle` and the `/` snapshot route go).

## 6. State (2026-10-28)

**The grammar (A0) is done.** Every verb of the four tables is data in `shell_grammar.rs` (69
verbs, 203 leaves); the shell parses through `parse`/`parse_line`; `help`, `usage_of` and Tab
completion read it; the body renders every form from the leaves (effect → outcome class, dangerous
switches as explicit ticks, required flags as required fields, `Rest` as free text). **Parity is a
journey row**: `/verb/NAME/dry` plans every leaf's filled form with `mini shell --line L --plan`;
zero usage refusals over 203 leaves, red-proofed by a verb the shell lacks; the spine rows assert
decoded outcomes.

**What landed, with shas.**

| what | sha |
|---|---|
| Progressive `can`: the grants page judges one grant per request as each answer lands; a bare `can` ends with "N of M grants judged within 100 s", never a 504 | `fe1cf181`, `db61a971` |
| The body's deadline never cuts a transition short (it runs to its decision; the page says undecided with where it lands); a read stopped at 100 s is stopped with its whole process group | `9b03c4e6`, `43533e6d` |
| The tour runs no shell itself (its purse meter loads after the page) | `890d2b3d` |
| `jtour` asks `can DOC`, waits the body deadline + 30 s on step 4's own outcome, prints `step4-ms`, expects `answered` | `575e1b21` |
| The door: "Pay with your wallet" (vendored @solana/web3.js 1.99.0 and the sol-misc adapter, pinned by sha256; transfer + memo built from the quote, signed by the wallet, sent from the browser, the signature posted; the paste path stays) | `b3da2198` |
| The door: the free route names the configured funding; the enrolled status says what was funded | `da4bed53` |
| The door's pay-page audit fixes: only new requests spend the per-source budget (4); amount in tokens and the quote's chain hour (5, 3); the adapter asks for the quote's cluster (7); a door refusal is said with the signature, the signature shown before the POST, a stale quote refused, a signed transaction that differs from the built one refused (1, 2, 3, 6) | `861fe953`, `b4a1a9d6`, `3710db83`, `37f23dfc` |
| Export my world: `export world [NAME]` → `mini export-world` (reads only: every reference; each document as rendered and its signed view; every attempt with its standing; room state; public key and custody statement; a manifest with the world root and a sha256 per file); `/export` starts it in the background, Download streams it through the gateway and deletes it; a notice on the front page from 10 November; the read stamp carries the world root | `370d606e`, `071aaf95` |
| Subscribe: what the tier buys from the `zai-glm` provider row (model, member calls a day and until the weekly reset), ember's policy line as a marked placeholder, price and period, purse meter, the window end as a UTC date, `pay subscribers week`, the join from the inbox invitation; front page and rail | `0ac2e8df` |

**Research consent** (ember's policy ruling): the fact is the reference `research-consent` in the
member's own workspace, a declared cell under the open law, **field 1 = 1 for CC0** (contributed
for research) **and 0 for none**. The door's form carries the sentence (`deploy/policy/RETENTION.txt`,
the one copy the door and the body read) and an unchecked "contribute my data for research (CC0;
kept private until reviewed)"; the processor writes the fact at enrolment as the member's own turns
(`create research-consent declared open 1`, `invoke research-consent-0 research-consent create 1 V`,
`submit research-consent-0`; a retried tick resumes) and the status carries `researchConsent`
(`0bf68599`). `/export` shows the value by a signed read, with the sentence, and records a change as
a compare-and-write on field 1; `/subscribe` carries the sentence; the export manifest carries
`researchConsent` cc0 | none | unrecorded (`33c13554`). Rows: consent-enrol, consent-flip,
export-consent.

**Abuse limits** (infra's review, edge/demo/ABUSE-LIMITS.md): beside the gateway's 64 connections,
a member holds at most 4 body requests at once; a fifth is refused with a 429 page that says so
(`90f7f959`, `limits.rs`, tested: the fifth refused while another member proceeds). One export per member per 10 minutes, the shell's mechanism on both faces: `mini export-world`
claims HOME/exports/.last-export (the unix second the last export began, locked while one runs;
a failed export puts the previous start back), and /export asks the same rule first without
claiming (`world_export::may_export`), so a refusal is a 429 page in the shell's own words (one
running, inside the window naming when the last began and when the next may, an unreadable file)
with the last archive's sha256 (NAME.sha256, written beside it and kept after the download).

**Box verification** (dregg-build, the round-2 candidate, the long-lived world `wf-jrun3`, at
`a0f9c246`): door tests 9 + 8 green under node; JWF 43/48 with export end to end (start, ready,
download, deleted on the box, the appended text in the archive, manifest height 425 and world root
equal to the live page's), `subscribe-page`, and `tour-chromium` (step 4 answered in 91 s). The
one row-order red (`receipt-anchor` read a page the new rows had replaced) is fixed in `abf33668`.

**Four story rows stay strict.** `story-invite`, `story-join`, `story-move`, `story-refused` failed
on that run because `story invite` (a transition) outlasted the body's 100 s and answered
"still deciding": the rows still assert admitted / answered / refused, because those are what a
member sees on a world that answers in time, and the cut gate runs on a fresh one. Loosening them
to accept "still deciding" would make the tour's door 11 green while showing a member nothing.
`story new` (nineteen transitions in its template) is the one step the journey waits out by
retrying the seal, because its length is the template's, not the world's.

**The aged world, published** (dregg-build at load 12–25 on 8 cores, `wf-jrun3` after about twenty
JWF runs, the member holding 124–169 references and about 7,100 attempts): `mini shell` start 51 s;
`can DOC` (one reference) 6 min 3 s before the first verdict, then about 10 s per verb; `story new`
about 4 min (nineteen transitions, about 5–12 s each); the export of 169 references 317 s
(385 MB). The tail bound (L = 256) is reached without the operator's checkpoint timer: the box
runner certifies every 30 s when the uncertified tail is at least 64, as the box's timer does.
These are numbers, not a gate.

**Faces for the 10-28 member verbs** (lane/web-parity `6d0f878a`, on main at `0d7af4da`). Each goes
through the derived path: a place's page embeds the real grammar forms with what the place knows filled
in (`verbs::form_for_filled`, prefill keys as `/verb/NAME?key=` uses), and a computed control speaks the
verb's grammar through the one assembler (`verbs::assemble_named`); every answer is the one outcome
partial.

| face | where | what it draws and does |
|---|---|---|
| Programs | `/bend`, `/bend/await/O/T` (`web/programs.rs`; rail) | the workspace's bend registry (`bend/objects/*.json`); any activity read by the shell's `bend await` as phase, slot, decider, deadline, declared state; the slot's decider gets the `bend answer` form with SLOT filled, anyone else is told the answer is refused `notDecider` |
| What Hermes may do here | `/room/R/resident#hermes-tools` (`web/resident.rs`) | the room's `hermes/tools` bits (files 1, terminal 2, python 4, oracle 8) and `hermes/compute` from the room's own signed view; the founder (roster field 2000) gets checkboxes whose sum becomes `tariff R set hermes/tools N` (and `hermes/compute N`), one line per changed field; others see who sets it |
| Explained refusals | `body::EXPLAINED` | `oracle-not-granted` (links to the grant), `oracle-not-configured`, `await-not-in-room`, `notDecider`, `member-day-ceiling`, `member-total-ceiling`: said with their meaning in any outcome partial and under a resident's reply |
| Stories | `/story` (`web/stories.rs`; rail), the member's front page, the door's status page | invitations in `HOME/requests` (where the door hands the tale's) with `story join NAME @FILE` filled; an invitation to someone else listed without a form; stories held (`HOME/story`) with enter and invite; the front page's "You are invited to play" notice; the door's status says joined / invited / stopped (with the processor's reason) and links to `/story` |
| Thin-birth display | none | no web face shows a consent display (thin or not), so `thin-display.json` has none; the receipt page could show it beside the anchor (the file is in the attempt directory) if one is wanted |

Not drawn, and why: the operator's sandbox ceiling (`controller.json` `sandbox`, 0600 under the
resident's user) is not readable by a member's body; the page says the effective set is ceiling ∩
grant and that the ceiling is not in the room's read. Publishing it would take an operator-side file
(like `/etc/mini/providers.json`), not a Host read.

Rows: JWF `hermes-tools-{none,grant,revoke,refused}`, `bend-{programs,await-read,answer-refused}`,
`story-page-{invited,joined}`, `story-front-notice`, `story-join-refused`; `story-join` now posts the
`/story` page's own filled form. J14_ORACLE checks bob's resident page explains `oracle-not-granted`
and shows the Oracle bit before and after the founder's grant. **Verified** (dregg-build, the J0-J8 world on candidate 76758dba6's Host with
this lane's `mini`, `mini-web`, `mini-web-spawn` at `588855a7`, `/build/lanes/web-parity/tour.sh`): JWF **62/62 PASS**,
every new row included; the first run (57/5) found the unrostered-room form and a row-helper slice, both
fixed in `588855a7`. Mac: the filtered unit tests (faces, red-team over the new routes, door status) and
`check-fouc --only app` 12/12. **Not run:** the J14_ORACLE web checks (they need the Oracle
route fragment and upstream Hermes; whoever runs J14_ORACLE runs them) and `bend answer` admitted from
the web (the template world pins no Objective invocation policy, so no program opens a slot there; the
admitted answer stands on the card's unit test and J14_AWAIT's shell rows).

**What waits on others.** L4: the resident page names its route once the room records it (a room
fact such as `hermes/route`; today the room cell has no such field); the Join button takes the
founder-signed invitation once the concierge drops it into HOME/inbox (Option A, not on
`54a43e15`), matched by content (a room grant to this subject on the room's target), not by file
name. ember: the policy sentence on the Z.AI coding plan's terms, for the line marked
`data-owner="ember"` on `/subscribe`.
