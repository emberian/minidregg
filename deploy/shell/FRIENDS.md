# the mini shellserver: a guide for friends (from ember)

**what this guide is true of.** it describes the code in main (the minidregg repository,
commit 5216e02f), and says in each section whether the public node has it. the public node
(`mini@2.28.141.27`) runs candidate **5688775a** (a source commit of 2026-09-30, re-genesised
2026-10-01); that was read from the node on 2026-10-03. `help guide` on the node prints the
copy of this file that shipped with that candidate (`ship.sh` installs each candidate's own
`deploy/shell/FRIENDS.md`), so what the node prints is an older text than this one. when a
newer candidate is shipped, the table below is the part to redo.

## what the public node has, and what only main has

on the node today, the shell answers these verbs and no others (the `VERBS` table of
`native/resource-client/src/shell.rs` at 5688775a): `whoami keygen init enroll refs read
describe import create propose invoke delegate law submit lookup retry publish revoke doc
board inbox export history help exit`. inside them, `doc` has only `new` (a `draft` or a
`note`), `show`, `append`, `edit`, `link` and `backlinks`; `law` takes one JSON predicate;
`create` takes no field list; `keygen` makes one key and no next key.

| in this guide | on the public node | where it stands |
|---|---|---|
| keys, `init`, `create`, `invoke`, `delegate`, `publish`, `export`/`import`, `retry`, `revoke`, JSON laws, `lock`, `history` | yes (with the limits above) | the journey J0-J8 passed through this shell (`docs/evidence/2026-09-30-shell-journey`) |
| next key: `key-status`, `rotate-key`, `adopt-next-key` | no | main only |
| `renounce`, `inspect`, `why`, `can`, one-line laws, `law check`, `law show` | no | main only |
| documents beyond `new/show/append/edit/link/backlinks`: `insert`, `move`, `mark`, `annotate` in the shell, ranges, transclusion, `history`, `diff`, `pull`/`push`, `search`, `--at`, `--html`, `--raw` | no | main only |
| `mini web` (a command of the client binary, not a shell verb) | no | main only |
| proxy mode (`mini --remote`, `mini join`, `mini socket-proxy`) | no: the 5688775a source has none of them | main only; see its section for what it still needs |
| rooms, templates, `room leave` | no | integrated on development worlds only (README, Honest state) |
| chat (`chat`, `say`, `tail`, `react`, `topic`, `pin`) | no | compiled; no recorded run joins it to a native Host |
| a paid week in a room (`pay`, `credit`, `tariff`, `topup`, `room status`) | no | J17 passed on a development world |
| private rooms | no | on main; no run on a real Host is recorded in `docs/evidence`; devnet quality, privacy not audited |
| jobs, sealed markets | no | on main |
| the librarian (`summon`, `ask`, `dismiss`, `hermes`) | no: no such verbs, and `mini-hermes` was inactive | scripted-provider run on a private Store only |
| the Discord entrance | no: `mini-discord` was inactive and no Discord application exists | tested against a simulated Discord |
| paying to enrol (`mini join --solana`) | no: the pay watcher and roster sync were inactive, and the node's single-socket entry has no operator socket | fixtures only; see "joining by yourself" |

on 2026-10-03 the node's roster held ember and three test keys, and no friend was enrolled.

## beta, read this first

the store is a devnet. when the data model or the kernel wire changes it is re-genesised:
your ssh key and your signing key stay, and everything you made goes (resources, grants,
history). ember announces it, enrolls you again, and you redo your first 10 minutes with new
IDs (`deploy/shell/OPERATOR.md`, "Re-genesis"). nothing here has an uptime promise.

**key custody (hosted shell).** your dregg signing key is made *on the box*, in your session
home, and the box's operator (root) can always read it. who else can depends on how the box is
set up, and ember tells you which:

- **one shared account** (the public node today): the Store, the Host, the operator's tools and
  every hosted friend's session run as the box's `mini` account, so the shell's verb grammar is
  the only fence between friends (`deploy/shell/README.md`).
- **separate accounts** (dregg-infra `tenancy=split`, built on main 2026-10-04, on no box yet):
  your session runs as your own account `mini-s-NAME`, and only that account and root can read
  your session home; the Store and the Host run as `mini-core`, which cannot read it either. a
  provider key you `key set` is sealed by the box's key broker (`mini-keys`), which no session
  account, not the Store and not the librarian can read: it checks your grant and makes the
  provider call itself. a Discord line runs as your account too.

enrollment also needs your key in ember's session for a moment, because `enroll plan` signs
with both keys in one process; ember copies it there and deletes the copy right after the
enrollment (`OPERATOR.md`, steps 4-5). keep nothing precious behind a hosted key. proxy mode
(below) keeps your key on your own machine; main has it, the node does not.

**your next key (main only).** `keygen mini.key` also makes `mini.key.next`: your *next* key.
your record commits to it (only its digest is stored), and it is the only thing that can
rotate your identity: `rotate-key mini.key.next` makes `mini.key.next` the signing key of your
subject, the old key's writes are refused (the Host reports `bad-signature` and the client
adds that the key is not the subject's current key), your grants and resources stay yours,
and `mini.key.next` then holds the key after it. someone who steals `mini.key` cannot rotate
you away, because the Host refuses any rotation to a key whose digest isn't the one you
committed, whatever the stolen key signs. but **it protects you only once the next key is
not on the box**: while `mini.key.next` sits beside `mini.key` there, root and anyone who
takes one file takes both. no shell verb copies a key off the box or puts one back, so in the
hosted shell only ember (root) can move `mini.key.next` off the box and back for a rotation;
with proxy mode both keys stay on your machine. `key-status` shows your key epoch and whether
a next key is committed.

## what this is

mini is a small store of owned resources. every action is a signed request the Host (written
in Lean) admits or refuses; admitted ones leave a receipt. you use it through `mini shell`
over ssh: one verb is one client operation, and a refusal names its reason (`why` explains
the last one you hold; a `law-denied` refusal can name no clause).

## getting in

1. make an ssh key just for this: `ssh-keygen -t ed25519 -f ~/.ssh/mini`
2. send me `~/.ssh/mini.pub` (the `.pub` one, only that) and the name you want for your
   session: it must start with a lowercase letter, then lowercase letters, digits and `-`,
   32 characters at most, and it is permanent.
3. when i say you're on the list: `ssh -t -i ~/.ssh/mini mini@2.28.141.27`. you land at
   `mini> `. (on a box with separate accounts, the login is your own: `mini-s-NAME@HOST`, NAME
   being your session name; everything after the login is the same. typing `mini@` there tells
   you the right login and runs nothing.) Tab completes verbs and names, Up/Down walks history, `help` lists every verb,
   and `help VERB` shows what it runs.

```
ssh -t -i ~/.ssh/mini mini@2.28.141.27                 # interactive
ssh -i ~/.ssh/mini mini@2.28.141.27 'read notes'       # one verb; exit code is the verb's
ssh -T -i ~/.ssh/mini mini@2.28.141.27 < steps.mini    # a script, one verb per line, stops at the first failure
```

### keeping your key on your own machine (`mini --remote`): main only

the hosted shell above is a convenience, and a weak one for your key (see key custody).
**proxy mode** is the other mode: you run the same `mini` locally and the box only relays its
frames (it keeps what you store, not your key). the box side is a `mode=proxy` line in the
operator's roster (`deploy/shell/README.md`); it needs `mini socket-proxy`, which the node's
candidate does not contain, so **today there is no proxy mode on the public node.** what main
implements:

1. get `mini` from a candidate (Linux x86-64: `bin/mini`; macOS arm64:
   `bin/clients/aarch64-apple-darwin/mini`) and check its SHA-256 against `SHA256SUMS`.
2. put `Host mini-box` with your ssh key in `~/.ssh/config`, and ask me for a `mode=proxy` line.
3. the three commands (give `--verifier` an absolute path):

```
mini join --key ~/.mini/me.key
    # prints three lines: your Mini public key, your NEXT key's public half, and its
    # co-signature (me.key.next holds the secret half: move it off this laptop, to paper or a stick).
    # send me all three
mini --remote mini-box join --key ~/.mini/me.key --sponsor-plan offer.json --dir ~/.mini/box
    # offer.json is what i send back (my `enroll offer`); it is refused unless it commits to YOUR next key.
    # you sign possession; it prints a JSON object whose possessionSignature is what you send me
mini --remote mini-box join --key ~/.mini/me.key --welcome welcome.json --dir ~/.mini/box \
     --verifier /ABSOLUTE/PATH/TO/pinned/minidregg-host
    # welcome.json is my `enroll welcome`; without --verifier it errors and makes no workspace
```

then `mini --remote mini-box shell --workspace ~/.mini/box/workspace --home ~/.mini/home`
(absolute paths) is the same shell as the hosted one, running on your machine.

**what proxy mode still lacks.** main's client signs nothing until a consent provider that you
select on your own machine has rebuilt the exact bytes: three variables, always absolute
paths and always together: `MINI_LOCAL_HOST` (the native Host image, `bin/minidregg-host`),
`MINI_CONSENT_HOST` (`bin/minidregg-client-consent`) and `MINI_CONSENT_CONFIG` (the
deployment config, whose `storageRoot` names a Store you have admitted locally). the Linux
friend bundle (`bin/clients/x86_64-unknown-linux-gnu/`) carries the pair. but the provider is
a full peer: it replays the Store at `storageRoot` from genesis, and **there is no command
that hands a friend such a Store, so on a friend's own machine signing stays refused**; the
macOS client has no consent pair at all (`deploy/shell/README.md`, "Signing consent"). the
hosted shell on main does not need the variables: with a Host path and no
`MINI_CONSENT_HOST` the client takes `minidregg-client-consent` beside that Host.

## your first 10 minutes

```
mini> keygen mini.key            # your signing key, in your session home
   … on main this also prints two hex lines (your next public key and its co-signature):
     send me both, then tell me "done" …
   … i enroll you and give you a factory grant and a small funded account.
     i send you your subject number (a long decimal) …
mini> init mini.key SUBJECT      # your workspace; before i've provisioned you it says so and makes nothing
mini> whoami                     # "initialized": true, "subject": "<yours>"
mini> create notes declared {"type":"all","predicates":[]} 2
                                 # a resource of your own, under a permit-all law, whose field 2 you may write
                                 # → "type": "confirmed", "confirmation": "installed"
mini> invoke first notes create 2 1     # propose: set field 2 to 1 (nothing is sent yet)
mini> submit first                      # send it → installed
mini> read notes                        # the page now has field 2 = 1
mini> invoke second notes write 2 7 1   # write 7 where you expect 1 now
mini> submit second
```

on main, `create NAME STORAGE LAW` with no field list declares no fields, and writing field 2
is then refused by name (`undeclaredField 2`) before the law runs; the trailing `2` (or `1,2`,
`0-3`, or `open`) is the field list. the node's `create` takes no such argument.

give a friend a narrower grant (they tell you their subject from `whoami`):
```
mini> delegate give-sam notes SAMS-SUBJECT observe,mutate 50000
mini> submit give-sam
mini> publish give-sam
```
hand the reference over (it's JSON addressed to sam; `export` works once you have run `publish`):
```
you$ ssh -i ~/.ssh/mini mini@2.28.141.27 'export give-sam' > give-sam.json   # send them this file
sam$ ssh -i ~/.ssh/mini mini@2.28.141.27 "import notes $(cat give-sam.json)"
sam$ ssh -i ~/.ssh/mini mini@2.28.141.27 'read notes'
```
retrying is safe. after the service restarts, the same attempt returns the same receipt:
```
mini> retry first                # "confirmation": "replayed", same transactionId as before
```
laws. you can change the law and grants keep working:
`law v2 notes {"type":"not","predicate":{"type":"any","predicates":[]}}`, then `submit v2`.
this one still permits everything, and sam can still write. now lock it:
```
mini> law lock notes {"type":"any","predicates":[]} --allow-unsatisfiable   # "any of nothing": denies everything
mini> submit lock
mini> read notes                                       # refused: law-denied: sealed   (exit 3)
mini> law unlock notes {"type":"all","predicates":[]}  # refused: law-denied: …
```
that's the point: nobody can bypass it, not you as owner and not me. **a lock is
permanent**, so lock throwaway things. (on main `law` asks the Host first whether a law can
ever pass; a lock can't, so without `--allow-unsatisfiable` it stops you and says so.
the node's `law` does not ask.)

main only: can a law ever pass? ask before you install it. `law check` takes the one-line
grammar (clauses separated by `;`) or a JSON predicate:
```
mini> law check "field 1 <= 0; field 1 monotone; field 1 == 1"
UNSATISFIABLE: this law admits no step.
these clauses contradict:
  field 1 <= 0                 from clause [0] `field 1 <= 0`
  field 1 >= 1                 from clause [2] `field 1 == 1`
  (added up, they say 0 <= -1, which no value can make true)
mini> law check "verb == read"
satisfiable: admits e.g. verb = read
WARNING: this law admits no write.
  …                              # then the clauses that rule writes out, a `for you:` line, and a
                                 # WARNING that you could never change such a law once it is installed
mini> can --any board             # one write board's law admits, from its values now
board  law version N
  a write this law admits, from the cell as it is now:
    field 2 = 2    (now 1)
  paste:
    invoke ID board write 2 2 1
  [judged as: verb = write, subject = S, every other field unchanged]
```
`law ID REF …` runs the same check before it proposes anything: a law no step can satisfy
is refused on the spot, with the clauses that contradict (add `--allow-unsatisfiable` when
you mean it, as for a lock); a law that no request *by you* can ever pass is refused too
(`--i-lock-myself-out` installs it anyway); a law no write can pass is proposed with a
warning. the answer is the Host's (it decides the law's arithmetic exactly and hands back a
step it checked, or the contradiction), and asking proposes nothing. a law with
`ran`/`witnessed` or a hash commitment is outside what it can decide and says which clause;
a law of more than about ten independent `any [ … ]` clauses is too many cases and says so
too. `history` lists what you did and how each attempt ended. take a grant back with
`revoke cut notes SAMS-SUBJECT`, then `submit cut`; sam's next read is `refused: revoked`.

## documents

on the node you have `doc new`, `show`, `append`, `edit`, `link` and `backlinks` (and `board`).
everything below that is not in that list is main only. a doc is a resource whose lines you
write together; its lines stand in a tree (sections hold lines), and `doc show` walks it in
order:
```
mini> doc new paper                       # (or `doc new log note`: append-only, edits refused)
mini> doc append p1 paper 'first paragraph'
mini> submit p1
mini> doc insert paper 1 'a title'        # a line placed at line 1; the rest move down (no submit)
mini> doc show paper                      # numbered lines, marks, annotations, quotes inline
mini> doc edit p2 paper 2 'first paragraph, better'
mini> submit p2                           # refused if someone changed line 2 since your `doc show`
mini> doc mark paper 1 heading            # bold italic code heading, or `link TARGET`
mini> doc annotate n1 paper 2 'cite this'  # then `submit n1`; it goes stale if line 2 changes
mini> doc move paper 3 1                  # line 3 now stands where line 1 stood
mini> doc link p3 index paper             # a proposal (submit p3): a link from index to paper; `doc backlinks paper` finds it
mini> board new tasks                     # tasks 0 and 1: `board add`, `board take`, `board move … todo doing`
```
**quoting another doc without copying it.** whoever may write `notes` publishes a range of its
lines (`doc range notes 2 3`; the numbers are notes' live line numbers); you transclude it
into your doc: `doc transclude paper notes 2 3` (a snapshot, pinned to those lines as they are
now; the quote goes at the end unless you add `at N`) or `… live` (follows later edits; `doc
follow paper T` re-reads it, T being the id `transclude` printed). your doc holds no bytes of
notes: each reader sees the quote through their own read of notes, so someone without a grant
on notes sees `[transclusion: 2 atoms of notes, not readable by you]` instead. `doc backlinks
notes` lists your quote.

**the past.** `doc history paper` lists every write with its height and who made it;
`doc show paper --at 77` is the doc as it stood at height 77 (only if your grant covered it
then: otherwise `refused: no-grant`); `doc diff paper 77 81` names what changed, moves included.

**your own editor.** `doc pull paper` prints the live lines (a quote is one marker line,
`⟦transclusion T⟧`, which you may keep or delete but not edit). edit the text, then `doc push
p4 paper @p.md`: the push becomes the fewest edits, new lines and strikes in one proposal, and
is submitted in the same step. `@p.md` reads `requests/p.md` in your session home, which only
the operator can write on the hosted box; over ssh use stdin instead: `ssh … 'doc pull paper'
> p.md`, then `ssh … 'doc push p4 paper @-' < p.md`. if someone changed a line you edited since
your pull, the whole push is refused and the refusal names the line: pull again, merge, push
again.

**on the web.** `mini web --dir WORKSPACE --listen 127.0.0.1:0` is a command of the client
binary, not a shell verb: it runs where your workspace is, so a hosted friend has no way to run
it. it binds `127.0.0.1` only, refuses other `Host:` and `Origin:` headers, and puts every
page under a per-launch secret printed when it starts (use that URL). it serves your docs as
pages (a page is `doc show NAME --html` plus the links and backlinks), and it also serves forms:
editing a doc, creating a doc, and the Studio routes accept POST and go through your own client
and the Host like any other proposal. `doc show NAME --raw` prints the bytes of the lines and
nothing else.

share a doc the same way as `notes` (delegate, publish, export/import). `delegate` cannot
narrow a grant to fields; a reviewer who can mark and annotate but not edit needs a JSON
proposal with `"fields":["annotations"]`: `propose ID` followed by the JSON
`{"type":"minidregg-workspace-proposal-v1","action":"delegate","name":"paper","recipient":
"SUBJECT","verbs":["observe","mutate"],"maxCost":"50000","fields":["annotations"]}`, then
`submit ID` and `publish ID`.

## rooms (main only; not on the node)

a room is a resource that other things are born *in*; holding a grant under the room reaches
the room and everything in it. the verbs you'll use:
```
mini> room new lab                         # a bare room you found (`--law realm`: only you and any
                                           #   --referee you name place things; or start from a template, below)
mini> room invite i1 lab SAMS-SUBJECT      # one grant under lab: observe + place (add things)
mini> submit i1                            #   widen with --verbs observe,place,mutate,delegate;
mini> publish i1                           #   narrow with --fields 1,2 or --max-delta 7=50
mini> export i1                            # → the reference; sam runs `import lab <it>`
sam> doc new notes --in lab                # sam adds a doc to the room (so does `create … --in lab`)
mini> room members lab                     # who holds a standing grant under lab
mini> room kick k1 lab SAMS-SUBJECT        # then `submit k1`: sam's grant, and every grant sam
                                           #   handed on from it, is refused `revoked`
```
also `room list` (your rooms), `room law lab` (its current law). someone with no grant
under lab can't add anything to it: they get `refused: … notRoomMember`. the room's law
decides who may add things: changing it never revokes anyone's grant (the J7 rule), but a
law like `any [ not (verb == place), subject in {YOU} ]` stops everyone else adding
(`birthRefused`), while their reads keep working.

**leaving a room you joined is yours to do; nobody has to kick you.** `room leave l1 lab`,
then `submit l1`: you give up your grant under lab, signed with your own key, and no one
else's permission is asked. everything you handed on from that grant ends with it (the leave
lists what this workspace knows of: `ended with it: …`), so if you invited someone with it,
they're out too. after that your reads of lab are refused `revoked` and you can't add to it.
it's permanent: leaving twice is refused `alreadyRevoked`, and coming back means the founder
invites you again, which is a new grant. a founder's `room leave` is refused (it would give up
the owner grant); the founder uses `renounce` explicitly. `renounce r1 REF` (or `renounce r1
CAPABILITY-NUMBER [object|account|program]`) works for any grant you hold, room or not, then
`submit r1`. you can only give up what's yours: renouncing someone else's grant is refused
`notHolder`, and it tells you nothing about theirs. `renounce` takes no `--i-know`.

start a room from a template. `room new lab --template workroom` founds lab *with a map*, and
adopts lab for chat (`chat adopt lab`): `lab/index` (a doc everyone in the room reads and only
you write, and it only grows: its links are the room's map), `lab/wall` (a stream: what the
room says), `lab/notes` (a draft anyone with write in the room edits) and `lab/tasks` (a list
that only grows), linked from the index. the default invite gives observe and place only, so a
member needs `--verbs` with `mutate` to edit notes and `append` to write the wall. `doc show
lab/index` shows the map; `doc backlinks lab/wall` finds who points at the wall. `--template
social` is index + wall + intro, and `room welcome lab SAMS-SUBJECT --template social` invites
sam and bears sam a stream only sam may write (you pay for it and own it, but its law refuses
every writer but sam, you included). `--template story` is index + chapters (only grows) +
scenes (a stream only you write) + cast. a template is just the lines you'd type, in order,
with `$ROOM` and `$ME` filled in:
```
mini> room template list                   # workroom, social, story
mini> room template show workroom          # the file itself, every line a verb you know
mini> room new mine --template @my.shell   # your own copy, from HOME/requests/my.shell
```
the first line that doesn't end done stops the rest, and the shell says which line and why
(`refused: law-denied: …` with the clause); the lines before it stand. names under a room
are yours: `lab/index` is your reference's name (sam may call it anything), never a path.

## talking in a room (main only; compiled, no recorded native run)

a room is a place a few of you talk. whoever starts it is its founder:

```
mini> chat new commons                    # you found it; it becomes your current room
mini> chat invite commons 1279008242 bob  # prints a `chat join commons {…}` line: send it to bob
bob>  chat join commons {…}               # bob pastes the line you sent
mini> say hello, friends                  # no quotes needed; apostrophes are fine
mini> tail                                # the last 20 lines: #N, hHEIGHT, who, text
mini> say --re 3 agreed                   # a reply to #3     (say --to bob … addresses bob)
mini> react 3 +1                          # topic TEXT, pin N and unpin: anyone may type them, only the founder's count
mini> tail --follow                       # keep watching; ctrl-c stops
```
each of you writes only your own stream; the Host refuses a write to anyone else's, so
nobody can put words in your mouth, and a line once said stays said. `#N` numbers never
change. names are yours: `chat name SUBJECT bob` decides what *you* see. a line from
Discord shows as `WHO via discord NAME#ID: …`, where WHO is the bridge's subject as you
named it: the bridge said it, quoting someone. `help chat` has the rest.

## a week in a room (main only)

some rooms charge. a room's price is its **tariff** (`tariff lab`: `week` credit buys
`period` heights of membership); your balance is `credit`. paying is one line:

```
mini> credit                    # credit 1000  (a signed read of your account)
mini> pay lab week              # one turn: the week's price to lab's till, marked renew
mini> room status lab           # picks up the window the room's concierge issued you
mini> doc new notes --in lab    # a member places cells in the room until the window ends
```
the window is a grant with an end height; past it the Host refuses you `outside-validity`
and `room status` says ENDED. `pay lab week` again renews. a founder runs a room with
`room new lab --template workroom --concierge SUBJECT`, sets prices with `tariff lab set
week 100`, renews by hand with `room renew lab SUBJECT`, and funds the concierge's runner
account with `topup lab N` (when the room has a Hermes, a bare `topup` feeds Hermes's budget;
`topup lab N concierge` forces the concierge). a room whose week is 0 is free: `pay` files a
request instead. this is credit inside the Store; paying for it with tokens is "joining by
yourself", below.

## private rooms (main only; devnet quality; privacy not audited)

devnet quality; privacy not audited; founder-key pin is trust-on-first-use via the operator unless verified out of band. they need a client built at or after the founder-pin change: an older client has no founder pin and cannot join a private room, so do not use one. `room new lab --private` makes a room whose words the node
stores and, while it follows the protocol, cannot read: what you say in it is sealed on *your* machine
under the room key before it leaves, and the node only ever holds that key wrapped to each member.
so run `mini` on your own machine for it (in the hosted shell your key is a file on this box, and
so is the room key). your keys live in an encrypted file in your workspace: set
`MINI_KEYCACHE_PASSPHRASE`; without it you cannot found, invite, kick or say in a private room,
and reads show `[sealed under epoch N — you do not hold that key]` (you also see that marker for
an epoch you were never given, for example after a kick). joining takes one exchange with the
founder, directly (in person, or a channel the node does not carry):
```
founder> room new lab --private        # prints the room id, keys cell, founder key and its FINGERPRINT
sam$ mini workspace --action room-key --op recipient-record --room-id ROOM --keys-cell KEYS \
       --key-epoch N --founder-key FOUNDER-KEY --dir WS    # N is sam's current key epoch (`key-status`);
                                       # pins the founder key, prints its fingerprint on stderr
                                       # and sam's signed declaration on stdout: give that to the founder
founder> room invite i1 lab SAMS-SUBJECT @sam-declaration.json
                                       # the declaration saved as HOME/requests/sam-declaration.json; for a
                                       # private room this verb itself submits and publishes the grant, then
                                       # releases the key to sam; sam still needs your `export i1` and `import lab <it>`
founder> room kick k1 lab SAMS-SUBJECT # revoke + a fresh room key for everyone else:
                                       #   sam keeps what he could already read, gets nothing new
mini> room keys lab                    # the key epochs you hold;  `forget lab` deletes yours
                                       #   (a promise of this client only: the wraps stay in the keys cell)
```
compare the fingerprint sam's client prints with the one the founder's printed. if the founder key
reached sam through this node and nobody compared, the node could have handed sam its own key: the
pin is trust on first use. your keys live in an encrypted file in your workspace: set
`MINI_KEYCACHE_PASSPHRASE`; without it you see `[sealed under epoch N — you do not hold that key]`.
inviting a subject the operator lists as hosted (a friend who only uses the hosted shell, or hosted
Hermes) needs `--i-know`: it puts the room key on the box. the node still sees who is in the room,
who wrote when, and how big each line is (in 64-byte steps). a misbehaving node can hide a key change
from you until you have seen it once (after that your client refuses to go back), so a member who has
not synced since a kick can be kept on the old key. what a recorded wrap protects is post-quantum (the
room key is wrapped to an X25519 + ML-KEM-768 pair; the signatures that vouch for the founder are
not). if you are the founder and rotate your signing key, run `room transition` first (it hands the
room to your next key; members need no re-pin) -- `rotate-key` refuses until you do. a private room is
never mirrored to Discord. again: devnet quality; privacy not audited. details:
`deploy/shell/templates/room/private/README.md` and `docs/PRIVATE-ROOMS-DESIGN.txt`.

what can you do here? ask before you try (main only):
```
mini> can paper                  # each verb your grants cover on paper, asked of the Host, never sent
paper  object 1121… (document)  held: delegate, mutate, observe
  read      admitted   [signed resource read]
  write     admitted   [append one line]
  edit      admitted   [line 1 to its own text]
  …
mini> can board                  # under a law that only lets field 2 grow:
  write     admitted   [field 2: 1 -> 2 (up)]
  write     law-denied: field 2 monotone (before 1, after 0)   [field 2: 1 -> 0 (down)]
mini> can                        # every resource you have a reference to
mini> can paper --all            # also the verbs you don't hold, as noGrant
```
for each verb, `can` builds the smallest real request (the bracket says which), signs it,
and has the Host judge it exactly as it would judge a submit, then throws it away: nothing
is submitted and `history` doesn't list the probes (`history all` does). a verb you hold no
grant for isn't listed. a revoked grant lists nothing. a locked resource answers
`law-denied: sealed` for every verb.

## post a job, run a job (main only)

a job is a Nock program, an input and a price, posted in a room. you put the price in
escrow; a friend in the room takes it by putting up a bond at least that big, runs the
program on their own node and posts the answer. whoever holds the job (a post or a claim
makes the reference) can check it within the challenge window (60 seconds by default,
`--window` on `post`): the kernel runs the program itself on the job's input and compares,
digit for digit. if nobody checks before the window ends, the answer stands and is paid. a
right answer pays the provider price + bond; a wrong one (or none by the answer deadline, for a
claimed job) gives you your escrow back plus half their bond (the tariff's
`slashCallerPermille`, 500 by default), and the rest is burned.
```
mini> job post lab 9721…4782 --input 6 --price 1000 --deadline 600 --account purse --name j1
mini> jobs lab                            # the jobs you have posted or claimed in lab, and each one's state
(sam) mini> job claim 1681…7359 --room lab --bond 1000 --account purse --name j1
(sam) mini> job answer j1                 # sam's node runs it and posts the output
mini> job check j1                        # the kernel re-runs it: upheld, or slashed
mini> job settle j1                       # the money moves; settling again shows the same receipt
```
`job show j1` prints every field by name. `--deadline` is the answer deadline in seconds; the
claim deadline is half of it. the price and bond live in the Book under the job's own id until
the job settles; nobody, you included, can move them by writing the job.

sealed markets. you sell SUPPLY units to sealed bids (at most four); nobody, me included,
can read a bid before the close, because the Store holds only a commitment to it:
```
mini> market open fish 120 140 8          # bids sealed until height 119, reveals 120..139, settle from 140
mini> delegate g1 fish SAMS-SUBJECT observe,mutate 50000     # then submit/publish/export as for notes
sam>  bid fish 30 5                        # commits to (price 30, qty 5); the opening stays in sam's workspace
sam>  submit bid-fish
mini> bids fish                            # sam's slot shows `sealed sealed` until sam reveals
sam>  reveal fish r1                       # from height 120: writes the opening; the law checks it
sam>  submit r1                            # a reveal before 120, or an opening that doesn't match its commitment, is `refused: law-denied: …`
mini> market settle fish                   # from height 140 (founder only): fills by price, then by who bid first
mini> submit settle-fish
mini> law show fish                        # the market's law, in the one-line grammar
```
`settle` records the fills and the clearing price; no credit moves. a bid you never reveal
fills nothing. there is no deposit yet, so not revealing costs nothing: markets here are for
friends, not for strangers who might bid and walk away.

## a librarian in a room (main only; scripted-provider run only)

a room's founder can bring in the node's Hermes, an agent that holds only what it is given and
pays for each thing it writes from a budget the founder funds. it needs a Hermes the operator
has registered and a provider route (`deploy/hermes/README.md`); when the node was read,
`mini-hermes` was inactive.
```
mini> summon lab as librarian --budget 100   # founder: Hermes joins lab's roster with 100 credit
mini> ask lab what changed since 48          # a say addressed to Hermes; it answers in its stream
mini> topup lab 50                           # its budget ran out: it said so, and stopped
mini> dismiss lab                            # founder: its grants are revoked; the unspent budget
                                             #   comes back when Hermes next attaches, less the network fee
```
the librarian links every document in the room from `lab-index`, writes a digest of what was
said into `lab-digest` (one section per few new entries, three by default), and answers "since"
questions from the room's signed history. its instructions are a document in the room,
`lab-hermes-librarian`: you can read it, the founder can edit it. each write it makes costs the
room's `hermes/turn` price (`tariff lab`, paid into the room's till; a price of 0 makes the
turn free) plus the network fee; when its account can't pay, the Host refuses the turn and
Hermes says "out of budget" in its stream. it can't write anything it holds no grant on: ask
it to edit your document and the Host refuses it.

## joining by yourself: pay to enrol (not deployed)

this is how you would enrol without asking ember, by paying. **it does not run anywhere you
can use yet**: the pay watcher and the roster sync were inactive on the node when it was
read, the node's entry has no operator socket (self-enrollment needs one, so it needs a
re-genesis onto the ingress topology), and publishing the pin your client reads is the last
step of the operator's runbook, still ahead.
what is decided, from `deploy/pay/enrol-terms.json` and `deploy/pay/README.md`:

- the price is **50 DREGG per node week**, paid to the Solana address
  `5N2uUG4TEwvM4acjWRpZ981CJa4p5e9RcuAYQvuUZLp6` (a fresh devnet-quality key), in the token
  with mint `XkeTXo1125vz5H9svJpGiw4JvLbN8VmMu9cmMvspump` (Token-2022, 6 decimals; 1 atomic
  unit is 1 credit). the tariff counts hours, so its week is 49999992 atomic units (49.999992
  DREGG, 8 atomic units under 50); enrolling costs the one-time birth fee plus that, and the
  Host's own quote, which `mini join` prints, is the amount to send.
- you run `mini join --solana` on your machine. it makes (or takes) your Mini key there, signs
  two possessions, and prints the Host's quote (the price as birth fee + membership + spendable
  credit, and that the quote does not reserve the price), then the address, the mint, the amount
  in DREGG and in atomic units, the memo (400 bytes), a Solana Pay link and an `spl-token transfer`
  line; **it submits nothing**, you pay from your own wallet. send from a wallet you control, never
  an exchange: exchanges drop memos, and a transfer without the memo can fail enrollment; some
  wallets also drop the memo from a Solana Pay link, so check the memo is in the transaction
  before you sign, or use the `spl-token` line. your wallet, your ssh key and your Mini key are
  linked publicly and permanently on Solana. `mini join --wait` then polls the public enrollment
  view for your key and, once you are enrolled, prints your subject, your workspace, your account,
  your lease (the box hour it runs until) and the ssh line for your proxy key; `mini join --renew`
  prints the memo again with one week's amount. the v2
  memo (`--memo-version v2`) also commits to your next key; v1 does not.

```
mini join --solana --host HOST --config PINNED-CONFIG.json (--socket SOCKET | --bootstrap-url HTTPS-BASE | --quote QUOTE.json) --enrol ENROL.json --dir NEW-JOIN-DIR [--key MINI.key] [--ssh-key SSH-KEY] [--name NAME] [--weeks N] [--starter-credit N]
mini join --memo-version v2 --solana --host HOST --config CONFIG --bootstrap-url HTTPS/mini/v2 --enrol ENROL-V2.json --dir NEW-JOIN-DIR [--weeks N --starter-credit N]
mini join --wait --host HOST --config PINNED-CONFIG.json --socket SOCKET --dir JOIN-DIR [--signature TX-BASE58]
```
- `ENROL.json` is the pin ember publishes with the friend bundle; the client refuses a pin whose
  address differs from the box's book row at the enrollment index, and refuses the unset
  placeholder `EMBER_ENROL_ADDRESS`. `deploy/pay/render-enrol` writes it from
  `enrol-terms.json`.
- once the Host has seen your payment, the roster sync (every 60 seconds) gives you a
  *proxy* line (self-enrollment is proxy only), so you then need proxy mode, with the signing
  limits above. the line lapses when your lease ends: your subject, credit, grants and
  resources stay, you just cannot log in; paying the same memo again renews it
  (`dregg-infra` `edge/mini/README.md`, "Roster").
- a payment can also be *journalled* instead of enrolling you: no memo, a malformed memo, an
  amount below the price, or an ssh key already taken. nothing is minted then, and it is
  kept for ember to settle by hand.
- the operator's order of work is `dregg-infra` `edge/mini/SHIP-RUNBOOK.md`, section 10.
  publishing the pin is ember's own act, after a 1 DREGG dry run from his wallet.

## how things end

stdout is the answer. when a verb fails, stderr's first line starts with who decided (the
Host's own decoding follows it, indented):

| exit | first word | meaning |
|---|---|---|
| 0 | | done |
| 1 | `error:` | the client stopped; the Host wasn't asked or didn't answer |
| 2 | `usage:` | the line didn't parse (`help VERB`) |
| 3 | `refused:` | the Host said no, and says why (below) |
| 4 | `undecided:` | the Host didn't settle it; `lookup ID` asks again |

the reason after `refused:` is one of the Host's closed set (`Compiler/RefusalReason.lean`):
- `no-grant`: nothing you hold covers that resource and that operation.
- `unknown-key`: this key isn't enrolled (yet, or since the last reset).
- `law-denied`: the resource's current law says no (see the lock above).
- `revoked`: the grant you used, or one it came from, was revoked.
- `stale-root`: you signed against a state that has since moved; the client already re-plans
  automatically, so you see this only after its retries are exhausted.
- `stale-grant`: the grant's issuer or policy epoch has moved (after a key or authority change).
- `bad-signature`: the signature didn't verify for that key and that exact request; after a
  key rotation, the old key gets this.
- `malformed`: the request didn't decode, or didn't fit its operation.
- `operation-rejected`: you were authorized but the controller refused the operation.
- `conflict`: the transaction identity was already used.
- `outside-validity`: the grant's window (a room week, for one) is over.
- `law-input-range`: a law clause compares values outside the native order range.
- `tail-bound`: the node is past its tail bound and takes no writes until its next checkpoint.
- `undisclosed`: a refusal before you proved who you are, or of a write at admission: on purpose
  it names nothing on your channel (the operator's log names it).

the client adds a few of its own, for example `refused: stale-line:` when a `doc push`'s
pinned lines changed. refused frames are kept under `refusals/`.

## what to expect

- numbered fields and one scalar action per `invoke`; laws may be written in the one-line
  grammar or JSON (the node: JSON only). quote ranges name published lines, not spans within a
  line. IDs are write-once: pick a new one per request. `help guide` prints the guide that
  shipped with the node's candidate.
- jobs run Nock programs, and a check re-runs the program only when an answer is checked in its
  window. sealed markets take at most four bids and hold no deposit. the librarian needs an
  operator-registered Hermes.
- not built: Hermes as a game master (`summon … as gm` refuses), and a MUD (`deploy/shell/
  templates/mud` is data that was never run against a Host).

## reaching me

telegram @emberian, or ember@lunar.town. paste the whole `refused:`/`error:` block,
because it holds the Host's own decoding.

thank you for poking at it early. (｡◕‿◕｡)
