# the mini shell: a guide for friends (from ember)

**what this guide is true of.** the code in the minidregg repository. a box runs one shipped
candidate, and `help guide` in the shell prints the copy of this file that shipped with that
candidate (`FRIENDS_GUIDE` and the `Plan::Guide` arm in `native/resource-client/src/shell.rs`). verb names, arguments and flags are
not copied here: they are data in `native/resource-client/src/shell_grammar.rs` (`GRAMMARS`),
and the shell's parsing, `help`, Tab completion and the web forms all read it. `help` lists every
verb and `help VERB` prints the leaves of one with the operation each runs.

## where things stand

the box is `dregg-demo`, <https://demo.dregg.online>. it serves a rehearsal ship with every login
closed until the opening, and the door at `/join` is held closed with it (`docs/DEMO-PREFIX-2026-10-26.md`
§2, "Where we stand"). which surfaces are on (Hermes, Discord, pay-to-enrol) and which are not is
recorded there too, and the product a stranger is meant to meet is
`docs/DEMO-EXPERIENCE-2026-10-27.md` (its status column says live, landing or needs per surface).
until logins open, nothing below can be done on the box by a friend; the sections say what the
code does. the older node `dregg-workhorse` is not part of this guide.

the demo box is redeployed and may be re-genesised. your ssh key and the signing key the box made
for you stay; everything you made (resources, grants, history) goes, and you redo your first
minutes with new IDs (`deploy/shell/OPERATOR.md`, "Re-genesis"). there is no uptime promise, and
the box is shut down on 11 November 2026 (`deploy/web-frontend/INSTALL.md` §4, `MINI_WEB_SHUTDOWN`).

## getting in

1. at <https://demo.dregg.online/join> choose a session name: a lowercase letter, then lowercase
   letters, digits and `-`, 2 to 25 characters, never a reserved word, permanent
   (`deploy/door/README.md`, "Rate limits and abuse"). an ssh key is optional: paste the one-line
   public half of an `ssh-ed25519` key if you want ssh as well as the browser (FIDO, RSA and ECDSA
   keys are refused; `ssh_ed25519` in `native/discord-entrance/src/door.rs`). the paid route needs the ssh
   key (`Request::parse`). tick "link Discord" if you want a link code. keep the status page: its address is
   the only key to your request (`deploy/door/README.md`, "Trust boundary").
2. when the status page says the account is ready it shows a one-time web login link
   (`https://demo.dregg.online/login/CODE`, good for the door's `linkTtlHours`, 7 days by default;
   `deploy/web-frontend/INSTALL.md` §6) and, if you gave a key, the ssh line:

```
ssh -t -i ~/.ssh/mini mini-s-NAME@demo.dregg.online                 # interactive
ssh -i ~/.ssh/mini mini-s-NAME@demo.dregg.online 'read notes'       # one verb; the exit code is the verb's
ssh -T -i ~/.ssh/mini mini-s-NAME@demo.dregg.online < steps.mini    # a script, one verb per line
```

each `ssh` line opens a new connection, and the handshake (key exchange and authentication) is most
of a quick verb's time: about 180 ms on the box against 15 ms for the verb itself. running many
one-verb lines, keep one connection open and reuse it, in `~/.ssh/config`:

```
Host demo.dregg.online
  IdentityFile ~/.ssh/mini
  ControlMaster auto
  ControlPath ~/.ssh/cm-%C
  ControlPersist 10m
```

the browser face is the same session: forms for the verbs and a terminal pane over a WebSocket
running `mini shell` as your account (`deploy/web-frontend/INSTALL.md`, intro and §5). you land at
`mini> ` already enrolled and initialized (the door ran `keygen` and `init`, `deploy/door/README.md`,
"Trust boundary"). Tab completes verbs and names, `help` lists every verb. an operator friend is
added by ember instead (`deploy/shell/OPERATOR.md`).

## whose key, and who can read what

- **your Mini signing key is made on the box**, in your session home, by your own account
  `mini-s-NAME` (0700 home, 0600 files). the box's operator (root) can always read it and sign as
  you; the shell says so when it starts (`HOSTED_CUSTODY_BANNER` in `shell.rs`). the door's
  account shape is split tenancy: the Store and Host run as `mini-core`, the door's form as
  `mini-door`, and the door refuses to run without that shape (`deploy/door/README.md`, intro and
  "Custody contract"). no other file on the box holds your key; `journey.d/jdoor.sh --box` searches
  the box for your key bytes and fails if any file outside `sessions/NAME/` has them.
- **a provider key you `key set` is sealed by the box's key broker** (`mini-keys`), which no session
  account, not the Store and not Hermes can read; root can still use it (`deploy/hermes/README.md`,
  "Custody").
- **everything on the demo box is world-readable to its members**: what you store is readable by
  every other member, so keep nothing private or precious behind a hosted key
  (`website/join.html:34`).
- **the next key.** `keygen mini.key` also makes `mini.key.next`, your next key
  (`KEYGEN` in `shell_grammar.rs`). your record commits to its digest only, and `rotate-key mini.key.next`
  is the rotation (`ROTATE_KEY`); `key-status` shows the epoch and whether a next key is committed
  (`KEY_STATUS`). a stolen `mini.key` cannot rotate you away, but this protects you only once
  `mini.key.next` is not on the box: while the two sit side by side, one stolen directory takes both.
- **proxy mode keeps your key on your own machine** (`mini --remote`, `mini socket-proxy`): the box
  relays frames and holds no key that signs as you. the three commands, the consent variables
  (`MINI_LOCAL_HOST`, `MINI_CONSENT_HOST`, `MINI_CONSENT_CONFIG`) and the limit that on a friend's
  own machine signing stays refused until a locally admitted Store exists are in
  `deploy/shell/README.md` ("The friend's three commands", "Signing consent"); the box side is an
  operator-rendered `mode=proxy` line, which the door does not make.

## a short tour of the verbs

this is the order the demo shows them (`docs/DEMO-EXPERIENCE-2026-10-27.md` §1). every verb named
here is a leaf in `shell_grammar.rs` today; `help VERB` has the exact arguments.

- **documents**: `doc new`, `doc append`, `doc edit`, `doc link`, `doc transclude`, `doc show`,
  `doc history`, `doc diff` (the whole `doc` family is `DOC` in `shell_grammar.rs`; the line rendering
  is described in `deploy/shell/DOC-VERBS.md`). a write is a proposal and `submit ID` sends it:

```
mini> doc new paper
mini> doc append p1 paper 'first paragraph'
mini> submit p1                  # an outcome: admitted, refused or undecided
mini> doc show paper
```

- **what can I do, and why not**: `can REF` asks the Host, for each verb your grants cover, whether
  it would admit the smallest real request, and sends nothing; `can --any REF` prints one write the
  law admits from the values now, as a line to paste (`can_any` in `lawsat.rs`); `why` explains the last
  refusal you hold with the clause and slot values (`WHY` in `shell_grammar.rs`); `inspect law REF` shows
  the installed law (`INSPECT`); `law check "CLAUSE; …"` asks whether a law could ever pass before
  you install it (`LAW`). a verb you hold no grant for is not listed by `can`.
- **delegate, bounded**: `delegate ID REF RECIPIENT VERBS MAX-COST [--until H]` proposes a grant that
  ends at height H (`DELEGATE`); `submit ID`, `publish ID`, then `export ID` and the recipient's
  `import NAME <json>` hand it over; `revoke ID REF RECIPIENT` takes it back; `renounce` gives up a
  grant you hold, and `room leave` gives up your grant under a room.
- **an agent in a room**: `summon ROOM as librarian --budget N`, `ask ROOM text`, `tail`, `dismiss ROOM`
  (`SUMMON`, `ASK`, `TAIL`, `DISMISS`). it needs a Hermes the operator has registered and a provider route
  (`deploy/hermes/README.md`); on the demo box the Hermes controller is not standing yet
  (`docs/DEMO-PREFIX-2026-10-26.md` §2), so `summon` is not a thing you can run there until it is.
  `summon … as gm` is refused (`role` in `native/resource-client/src/hermes.rs`).
- **a lost reply**: an attempt whose reply never arrived is retained, `lookup ID` asks for the same
  decided outcome and `retry ID` sends the exact retained call; neither is ever a second write
  (`LOOKUP` and `RETRY` in `shell_grammar.rs`). `submit ID --lose-reply-once` makes your own client lose the reply on
  purpose, to try this (`SUBMIT`).
- **applications**: `apps search`, `apps show`, `apps install`, `apps open GRAIN`, `apps retry`
  (`APPS`). an app opens on its own origin `GRAIN.demo.dregg.online`; its grant boundary and the
  v1 one-guest-subject-per-grain limit are in `docs/DEMO-EXPERIENCE-2026-10-27.md` §1 step 7.

your first resource, from scratch (the door has already done `keygen` and `init`):

```
mini> whoami
mini> create notes declared {"type":"all","predicates":[]} 2
mini> invoke first notes create 2 1       # propose: set field 2 to 1 (nothing is sent yet)
mini> submit first
mini> invoke second notes write 2 7 1     # write 7 where you expect 1
mini> submit second
```

`create NAME STORAGE LAW [FIELDS|open]` declares which fields the cell may hold; writing a field it
does not declare is refused by name before the law runs (`undeclaredField` and the theorem
`undeclared_field_refused` in `Kernel/DeclaredResourceScalar.lean`), so the trailing `2` is not optional. `history` lists your attempts and how each ended,
`history all` includes the `can` probes.

**changing the law.** `law ID REF LAW` proposes a new law, after asking the Host whether it can ever
pass (`LAW` in `shell_grammar.rs`). a law no step can satisfy is refused unless you add
`--allow-unsatisfiable`; one that no request by you can pass needs `--i-lock-myself-out`
(`install_check` in `lawsat.rs`). the first word after `law` is a proposal id, not a verb:

```
mini> law lock notes {"type":"any","predicates":[]} --allow-unsatisfiable   # "any of nothing": admits nothing
mini> submit lock
```

**a lock is permanent**: nobody can change that law again, not you and not ember, so lock throwaway
things. grants keep working under a changed law, and a locked cell refuses every verb with
`law-denied`.

## rooms, chat, credit, jobs, markets, stories

these are verbs in the same grammar; read their leaves with `help VERB` rather than a copy here:
`room` (`ROOM` in `shell_grammar.rs`: new, invite, members, kick, leave, seal, templates, status,
renew, concierge), `chat` / `say` / `tail` / `topic` / `pin` / `react` (`CHAT`, `SAY`, `TAIL`, `TOPIC`, `PIN`, `REACT`), `pay` / `credit`
/ `tariff` / `topup` (`PAY`, `CREDIT`, `TARIFF`, `TOPUP`), `job` / `jobs` (`JOB`, `JOBS`), `market` / `bid` / `reveal` / `bids`
(`MARKET`, `BID`, `REVEAL`, `BIDS`), `story` / `look` / `go` / `take` / `act` / `narrate` (`STORY`, `LOOK`, `GO`, `TAKE`, `ACT`, `NARRATE`), `kind` / `program` /
`instance` (`KIND`, `PROGRAM`, `INSTANCE`), `board` (`BOARD`).

what the code says about each, in the scope it was run:

- **rooms**: a room is a resource that other things are born in; a grant under it reaches the room
  and what is in it. `room new NAME --template workroom|social|story` founds a room with a map; the
  templates are the typed lines in `native/resource-client/templates/room/*/template.shell`, and
  `room template show T` prints one. a founder's `room leave` is refused (use `renounce`). a person
  with no grant under a room who tries to add something is refused `notRoomMember`; a room law that
  stops them is `birthRefused` (`Refusal` in `Kernel/RoomBirthGate.lean`).
- **chat**: `chat new`, `chat invite`, `chat join`, `say`, `tail`. chat ran against a native Host in
  J14: rows 33-41 (`chat new`, `chat invite`, `chat join`), 64-66 and 88-89 (`say`) and 135 (`tail`)
  of `docs/evidence/2026-10-01-p-hermes-room/j14.tsv`, and the dedicated row set is
  `native/resource-client/journey.d/jchat.sh`. each of you writes only your own stream.
- **a week in a room**: a room's price is its tariff (`tariff ROOM`); `pay ROOM week` buys a
  membership window and `room status ROOM` shows it, `ENDED` once the window is over
  (the `my window: ENDED` line of `run` in `native/resource-client/src/credit.rs`). run once in `docs/evidence/2026-10-01-p-credit/`.
- **private rooms**: `room new NAME --private` seals words on your machine under a room key; devnet
  quality, privacy not audited, founder-key pin is trust-on-first-use. run it on your own machine
  (in the hosted shell the room key is a file on the box). the exchange with the founder, the
  passphrase variable and the limits are in `native/resource-client/templates/room/private/README.md`
  and `docs/PRIVATE-ROOMS-DESIGN.txt`.
- **jobs**: a Nock job with an escrowed price, a bonded claim and a checked answer; the challenge
  window defaults in `DEFAULT_WINDOW` in `native/resource-client/src/job.rs` and the slash split is the tariff's
  `slashCallerPermille` (`Tariff` in `Kernel/PayTariff.lean`).
- **sealed markets**: up to four sealed bids, settled by price then arrival (the module header of `native/resource-client/src/market.rs`); there
  is no deposit, so not revealing costs nothing.
- **stories**: `story new NAME --from tale` builds a table under the sealed story law; recorded in
  `docs/evidence/2026-10-01-p-story/` (J15). the MUD data under
  `native/resource-client/templates/mud/` is data; the one place a journey row uses it is
  the `MUD sheet birth` row of `native/resource-client/journey.d/jclock.sh` (a sheet born under `law.management ; law.sheet` against the clock
  law), and no shell verb plays a MUD realm.

## joining by yourself: paying instead of the free route

the door's pay route gives the same hosted account, paid for by you. the price is the tariff's, not
this guide's: `Kernel/PayTariff.lean` defines it and `deploy/pay/README.md` records the amount, the
birth fee, the receiving address and the memo rules; the page shows the Host's own quote for you to
send exactly, and says whether the deployment is on Solana mainnet or devnet. what the page asks of
you: a plain `ssh-ed25519` key (the route needs it), one `ssh-keygen -Y sign -n dregg-enrol@v2`
signature pasted back, a payment from a wallet you control (never an exchange, which drops memos),
and the transaction signature or the page's wallet button (`deploy/door/README.md`, "Two routes, one
processor"). your wallet, your ssh key and your Mini key are linked publicly and permanently on
Solana. a payment with a missing or malformed memo, too little, or an ssh key already taken is
journalled instead of enrolling you, and ember settles it by hand. the pay route runs on a box only
once the operator has set up the payment watcher; on the demo box PAY is off in the present rehearsal
(`docs/DEMO-PREFIX-2026-10-26.md` §2).

## how things end

stdout is the answer. when a verb fails, stderr's first line says who decided
(`EXIT_OK` to `EXIT_UNDECIDED` and `render` in `native/resource-client/src/shell.rs`):

| exit | first word | meaning |
|---|---|---|
| 0 | | done |
| 1 | `error:` | the client stopped; the Host wasn't asked or didn't answer |
| 2 | `usage:` | the line didn't parse (`help VERB`) |
| 3 | `refused:` | the Host said no, and says why |
| 4 | `undecided:` | the Host didn't settle it; `lookup ID` asks again |

the reason after `refused:` is one of the Host's closed set, defined with its sentence in
`RefusalReason` and `RefusalReason.describe` in `Compiler/RefusalReason.lean` (`no-grant`, `law-denied`, `revoked`, `stale-root`,
`outside-validity`, `undisclosed`, and the rest). `undisclosed` names nothing on your channel on
purpose. the client adds a few of its own, for example `refused: stale-line:` when a `doc push`'s
pinned lines changed, and `refused: not sent:` when a command was never forwarded
(`render` in `shell.rs`). `why` explains the last refusal you hold.

## what to expect

- IDs are write-once: pick a new one per request.
- laws are written in the one-line grammar (clauses separated by `;`) or as predicate JSON.
- `@FILE` arguments read `requests/FILE` in your session home; where a leaf takes `@-` it reads
  standard input instead, which is the way over ssh (`doc push ID NAME @-`, the `doc push` leaf in
  `shell_grammar.rs`).

## reaching me

telegram @emberian, or ember@lunar.town. paste the whole `refused:`/`error:` block, because it holds
the Host's own decoding.

thank you for poking at it early. (｡◕‿◕｡)
