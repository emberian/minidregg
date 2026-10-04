# the mini shellserver: a guide for friends (from ember)

**beta, read this first.** i will reset the store at least once this week (a data-model
cutover) and a few more times before Oct 13 (kernel wire changes). when i reset it, your
ssh key and your signing key stay, and everything you made goes: resources, grants,
history. i'll tell you before each one. after a reset i enroll you again, and you redo
your first 10 minutes.

**key custody.** your dregg signing key is made *on the box*, inside your session home,
and i'm root there, so i can read it. enrollment also needs a copy in my session for a
moment (the shell co-signs with both keys; a later step removes that). don't put
anything precious behind it yet. taking your key home to your own machine is planned.

**your next key.** `keygen mini.key` also makes `mini.key.next`: your *next* key. your
record commits to it (only its digest is stored), and it is the only thing that can
rotate your identity: `rotate-key mini.key.next` moves your subject to it, your old key
stops signing (the Host refuses it by name), your grants and resources stay yours, and
`mini.key.next` then holds the key after it. someone who steals `mini.key` cannot rotate
you away, because the Host refuses any rotation to a key whose digest isn't the one you
committed, whatever the stolen key signs. but **it protects you only once the next key is
not on the box**: while `mini.key.next` sits beside `mini.key` here, root (me) and anyone
who takes one file takes both. copy it home (or to a USB stick, or paper), delete it from
your session home, and bring it back only to rotate. `key-status` shows your key epoch and
whether a next key is committed.

## what this is

mini is a small store of owned resources. every action is a signed request the Host
(written in Lean) admits or refuses; admitted ones leave a receipt. you use it through
`mini shell` over ssh: one verb = one client operation, and a no always says why.

## getting in

1. make an ssh key just for this: `ssh-keygen -t ed25519 -f ~/.ssh/mini`
2. send me `~/.ssh/mini.pub` (the `.pub` one, only that) and the name you want for your
   session (lowercase letters, digits and `-`; it's permanent).
3. when i say you're on the list: `ssh -t -i ~/.ssh/mini mini@2.28.141.27` (no DNS name yet).
   you land at `mini> `. Tab completes verbs and names, Up/Down walks history, `help`
   lists every verb, and `help VERB` shows what it runs.

```
ssh -t -i ~/.ssh/mini mini@2.28.141.27                 # interactive
ssh -i ~/.ssh/mini mini@2.28.141.27 'read notes'       # one verb; exit code is the verb's
ssh -T -i ~/.ssh/mini mini@2.28.141.27 < steps.mini    # a script, one verb per line, stops at the first failure
```

### keeping your key on your own machine (`mini --remote`)

the hosted shell above is a convenience, and on this box today it is a weak one: your Mini
key lives in your session home, and every hosted friend, the Store, the Host and the
operator's tools all run as the one `mini` account. so root, the operator, AND any process
running as `mini`, which includes every other friend's session, can read your key and sign
as you; the shell's verb grammar is the only fence between friends. separate accounts per
session are designed but not deployed. until they are, keep nothing
you would not hand to the other friends in a hosted session. if you would rather your key
never leave your machine, use **proxy mode**: you run the same `mini` locally and the box
only relays its frames (it keeps what you store, not your key).

1. get `mini` for your machine from the candidate (Linux x86-64 `bin/mini`, macOS arm64
   `bin/clients/aarch64-apple-darwin/mini`) and check its SHA-256 against `SHA256SUMS`.
2. put `Host mini-box` with your ssh key in `~/.ssh/config`, and ask me for a **proxy**
   key line (`mode=proxy`) instead of a shell one.
3. the three commands:

```
mini join --key ~/.mini/me.key
    # prints two lines: your Mini public key, and your NEXT key's public half
    # (me.key.next: move it off this laptop, to paper or a stick); send me both
mini --remote mini-box join --key ~/.mini/me.key --sponsor-plan offer.json --dir ~/.mini/box
    # offer.json is what i send back; it is refused unless it commits to YOUR next key.
    # you sign possession and it prints a signature: send it
mini --remote mini-box join --key ~/.mini/me.key --welcome welcome.json --dir ~/.mini/box
    # welcome.json is my second reply; this makes your workspace
```

from then on `mini --remote mini-box shell --workspace ~/.mini/box/workspace --home ~/.mini/home`
is the same shell as the hosted one, every verb below, running on your machine.

## your first 10 minutes

```
mini> keygen mini.key            # your signing key, in your session home; then tell me "done"
   … i enroll you and give you a factory grant and a small funded account.
     i send you your subject number (a long decimal) …
mini> init mini.key SUBJECT      # your workspace; before i've provisioned you it says so and makes nothing
mini> whoami                     # "initialized": true, "subject": "<yours>"
mini> create notes declared {"type":"all","predicates":[]}
                                 # a resource of your own, under a permit-all law
                                 # → "type": "confirmed", "confirmation": "installed"
mini> invoke first notes create 2 1     # propose: set field 2 to 1 (nothing is sent yet)
mini> submit first                      # send it → installed
mini> read notes                        # the page now has field 2 = 1
mini> invoke second notes write 2 7 1   # write 7 where you expect 1 now
mini> submit second
```
give a friend a narrower grant (they tell you their subject from `whoami`):
```
mini> delegate give-sam notes SAMS-SUBJECT observe,mutate 50000
mini> submit give-sam
mini> publish give-sam
```
hand the reference over (it's JSON addressed to sam):
```
you$ ssh -i ~/.ssh/mini mini@2.28.141.27 'export give-sam' > give-sam.json   # send them this file
sam$ ssh -i ~/.ssh/mini mini@2.28.141.27 "import notes $(cat give-sam.json)"
sam$ ssh -i ~/.ssh/mini mini@2.28.141.27 'read notes'
```
retrying is safe. after i restart the service, the same attempt returns the same receipt:
```
mini> retry first                # "confirmation": "replayed", same transactionId as before
```
laws. you can change the law and grants keep working:
`law v2 notes {"type":"not","predicate":{"type":"any","predicates":[]}}`, then `submit v2`.
this one still permits everything, and sam can still write. now lock it:
```
mini> law lock notes {"type":"any","predicates":[]} --allow-unsatisfiable   # "any of nothing": denies everything
mini> submit lock
mini> read notes                                       # refused: law-denied: …   (exit 3)
mini> law unlock notes {"type":"all","predicates":[]}  # refused: law-denied: …
```
that's the point: nobody can bypass it, not you as owner and not me. **a lock is
permanent**, so lock throwaway things. (`law` asks the Host first whether a law can ever
pass; a lock can't, so without `--allow-unsatisfiable` it stops you and says so.)

can a law ever pass? ask before you install it:
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
mini> can --any board             # one write board's law admits, from its values now
  a write this law admits, from the cell as it is now:
    field 2 = 2    (now 1)
  paste:
    invoke ID board write 2 2 1
```
`law ID REF …` runs the same check before it proposes anything: a law no step can satisfy
is refused on the spot, with the clauses that contradict (add `--allow-unsatisfiable` when
you mean it, as for a lock); a law no write can pass is proposed with a warning. the answer
is the Host's (it decides the law's arithmetic exactly and hands back a step it checked, or
the contradiction), and asking writes nothing. a law with `ran`/`witnessed` or a hash
commitment is outside what it can decide and says which clause; a law of more than about
ten independent `any [ … ]` clauses is too many cases and says so too. `history` lists what you did and how each attempt ended.
take a grant back with `revoke cut notes SAMS-SUBJECT`, then `submit cut`; sam's next read
is `refused: revoked`.

documents. a doc is a resource whose lines you write together; its lines stand in a tree
(sections hold lines), and `doc show` walks it in order:
```
mini> doc new paper                       # (or `doc new log note`: append-only, edits refused)
mini> doc append p1 paper 'first paragraph'
mini> submit p1
mini> doc insert paper 1 'a title'        # a line placed at line 1; the rest move down
mini> doc show paper                      # numbered lines, marks, annotations, quotes inline
mini> doc edit p2 paper 2 'first paragraph, better'
mini> submit p2                           # refused if someone changed line 2 since your `doc show`
mini> doc mark paper 1 heading            # bold italic code heading, or `link TARGET`
mini> doc annotate n1 paper 2 'cite this'  # then `submit n1`; it goes stale if line 2 changes
mini> doc move paper 3 1                  # line 3 now stands where line 1 stood
mini> doc link p3 index paper             # a link from index to paper; `doc backlinks paper` finds it
mini> board new tasks                     # tasks 0 and 1: `board add`, `board take`, `board move … todo doing`
```
**quoting another doc without copying it.** the owner of `notes` publishes a range of its
lines (`doc range notes 2 3`); you transclude it into your doc: `doc transclude paper notes 2 3`
(a snapshot, pinned to those lines as they are now) or `… live` (follows later edits; `doc
follow paper T` re-reads it). your doc holds no bytes of notes: each reader sees the quote
through their own read of notes, so someone without a grant on notes sees `[transclusion: 2
atoms of notes, not readable by you]` instead. `doc backlinks notes` lists your quote.

**the past.** `doc history paper` lists every write with its height and who made it;
`doc show paper --at 77` is the doc as it stood at height 77 (only if your grant covered it
then: otherwise `refused: no-grant`); `doc diff paper 77 81` names what changed, moves included.

**your own editor.** `doc pull paper` prints the live lines (a quote is one marker line,
`⟦transclusion T⟧`, which you may keep or delete but not edit). save it to `requests/p.md`, edit,
then `doc push p4 paper @p.md`: the push becomes the fewest edits, new lines and strikes in
one proposal. if someone changed a line you edited since your pull, the whole push is
refused and the refusal names the line: pull again, merge, push again.

**on the web.** `mini web --dir WORKSPACE --listen 127.0.0.1:0` serves your docs as read-only
pages on your own machine; a page is exactly what `doc show NAME --html` prints, plus the
links and backlinks. `doc show NAME --raw` prints the bytes of the lines and nothing else.

share a doc the same way as `notes` (delegate, publish, export/import). a reviewer you
delegate with fields `annotations` can mark and annotate but not edit.

rooms. a room is a resource that other things are born *in*; holding a grant under the
room reaches the room and everything in it. the five verbs you'll use:
```
mini> room new lab                         # a bare room you found (`--law realm`: only you
                                           #   place things; or start from a template, below)
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

**leaving a room is yours to do; nobody has to kick you.** `room leave l1 lab`, then
`submit l1`: you give up your grant under lab, signed with your own key, and no one else's
permission is asked. everything you handed on from that grant ends with it (the leave says
which: `ended with it: …`), so if you invited someone with it, they're out too. after that
your reads of lab are refused `revoked` and you can't add to it. it's permanent: leaving
twice is refused `alreadyRevoked`, and coming back means the founder invites you again, which
is a new grant. the same verb works for any grant you hold, room or not: `renounce r1 REF`
(or `renounce r1 CAPABILITY-NUMBER [object|account|program]`), then `submit r1`. you can only
give up what's yours: renouncing someone else's grant is refused `notHolder`, and it tells
you nothing about theirs. an agent you run (Hermes) gives up a grant it was handed the same
way; giving up authority never needs `--i-know`.

start a room from a template. `room new lab --template workroom` founds lab *with a map*:
`lab/index` (a doc everyone in the room reads and only you write, and it only grows: its
links are the room's map), `lab/wall` (a stream: what the room says), `lab/notes` (a draft
anyone with write in the room edits) and `lab/tasks` (a list that only grows), linked from
the index. `doc show lab/index` shows the map; `doc backlinks lab/wall` finds who points at
the wall. `--template social` is index + wall + intro, and `room welcome lab SAMS-SUBJECT
--template social` invites sam and bears sam a stream only sam may write (you pay for it,
sam owns it). `--template story` is index + chapters (only grows) + scenes (a stream) + cast.
a template is just the lines you'd type, in order, with `$ROOM` and `$ME` filled in:
```
mini> room template list                   # workroom, social, story
mini> room template show workroom          # the file itself, every line a verb you know
mini> room new mine --template @my.shell   # your own copy, from HOME/requests/my.shell
```
the first line that doesn't end done stops the rest, and the shell says which line and why
(`refused: law-denied: …` with the clause); the lines before it stand. names under a room
are yours: `lab/index` is your reference's name (sam may call it anything), never a path.

## talking in a room

a room is a place a few of you talk. whoever starts it is its founder:

```
mini> chat new commons                    # you found it; it becomes your current room
mini> chat invite commons 1279008242 bob  # prints a `chat join commons {…}` line: send it to bob
bob>  chat join commons {…}               # bob pastes the line you sent
mini> say hello, friends                  # no quotes needed; apostrophes are fine
mini> tail                                # the last 20 lines: #N, hHEIGHT, who, text
mini> say --re 3 agreed                   # a reply to #3     (say --to bob … addresses bob)
mini> react 3 +1                          # topic TEXT, pin N and unpin are the founder's
mini> tail --follow                       # keep watching; ctrl-c stops
```
each of you writes only your own stream; the Host refuses a write to anyone else's, so
nobody can put words in your mouth, and a line once said stays said. `#N` numbers never
change. names are yours: `chat name SUBJECT bob` decides what *you* see. a line from
Discord shows as `bridge via discord NAME#ID: …`: the bridge said it, quoting someone.
`help chat` has the rest.

## a week in a room

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
week 100`, renews by hand with `room renew lab SUBJECT`, and funds the concierge with
`topup lab N`. a room whose week is 0 is free: `pay` files a request instead.

private rooms (devnet quality; privacy not audited; founder-key pin is trust-on-first-use via the operator unless verified out of band.) they need a client built at or after the founder-pin change; an older client trusts whatever key wraps the box serves, so do not use one for a private room. `room new lab --private` makes a room whose words the node
stores and, while it follows the protocol, cannot read: what you say in it is sealed on *your* machine
under the room key before it leaves, and the node only ever holds that key wrapped to each member.
so run `mini` on your own machine for it (in the hosted shell your key is a file on this box, and so
is the room key). joining takes one exchange with the founder, directly (in person, or a channel
the node does not carry):
```
founder> room new lab --private        # prints the room id, keys cell, founder key and its FINGERPRINT
sam$ mini workspace --action room-key --op recipient-record --room-id ROOM --keys-cell KEYS \
       --key-epoch N --founder-key FOUNDER-KEY --dir WS    # pins the founder key, prints its fingerprint
                                       # and sam's signed declaration: give that to the founder
mini> room invite i1 lab SAMS-SUBJECT @sam-declaration.json   # the grant, then the key released to sam (hosted? add --i-know)
mini> room kick k1 lab SAMS-SUBJECT    # revoke + a fresh room key for everyone else:
                                       #   sam keeps what he could already read, gets nothing new
mini> room keys lab                    # the key epochs you hold;  `forget lab` deletes yours
```
compare the fingerprint sam's client prints with the one the founder's printed. if the founder key
reached sam through this node and nobody compared, the node could have handed sam its own key: the
pin is trust on first use. your keys live in an encrypted file in your workspace: set
`MINI_KEYCACHE_PASSPHRASE`; without it you see `[sealed under epoch N — you do not hold that key]`.
inviting a hosted subject (a friend who only uses this shell, or hosted Hermes) needs `--i-know`: it
puts the room key on the box. the node still sees who is in the room, who wrote when, and how big each
line is (in 64-byte steps). a misbehaving node can hide a key change from you until you have seen it
once (after that your client refuses to go back), so a member who has not synced since a kick can be
kept on the old key. what a recorded wrap protects is post-quantum (the room key is wrapped to an X25519 + ML-KEM-768 pair; the signatures that vouch for the founder are not). if you are the founder and rotate your signing key, run `room transition` first (it hands the room to your next key; members need no re-pin) -- `rotate-key` refuses until you do. a private room is never mirrored to Discord. again: devnet quality; privacy not audited. details: `deploy/shell/templates/room/private/README.md`.

what can you do here? ask before you try:
```
mini> can paper                  # each verb your grants cover on paper, asked of the Host, never sent
paper  object 1121…  held: delegate, mutate, observe
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
is written, no attempt is used up, and `history` doesn't change. a verb you hold no grant
for isn't listed. a revoked grant lists nothing. a locked resource answers
`law-denied: sealed` for every verb.

**post a job, run a job.** a job is a Nock program, an input and a price, posted in a
room. you put the price in escrow; a friend in the room takes it by putting up a bond at
least that big, runs the program on their own node and posts the answer. anyone in the
room can check it: the kernel runs the program itself on the job's input and compares,
digit for digit. a right answer pays the provider price + bond; a wrong one (or none by the
deadline) gives you your escrow back plus half their bond, and the other half is burned.
```
mini> job post lab 9721…4782 --input 6 --price 1000 --deadline 600 --account purse --name j1
mini> jobs lab                            # what's posted in lab, and where each one is
(sam) mini> job claim 1681…7359 --room lab --bond 1000 --account purse --name j1
(sam) mini> job answer j1                 # sam's node runs it and posts the output
mini> job check j1                        # the kernel re-runs it: upheld, or slashed
mini> job settle j1                       # the money moves; settling again shows the same receipt
```
`job show j1` prints every field by name. the price and bond live in the Book under the
job's own id until the job settles; nobody, you included, can move them by writing the job.
sealed markets. you sell SUPPLY units to sealed bids; nobody, me included, can read a bid before
the close, because the Store holds only a commitment to it:
```
mini> market open fish 120 140 8          # bids sealed until height 119, reveals 120..139, settle from 140
mini> delegate g1 fish SAMS-SUBJECT observe,mutate 50000     # then submit/publish/export as for notes
sam>  bid fish 30 5                        # commits to (price 30, qty 5); the opening stays in sam's workspace
sam>  submit bid-fish
mini> bids fish                            # sam's slot shows `sealed sealed` until sam reveals
sam>  reveal fish r1                       # from height 120: writes the opening; the law checks it
sam>  submit r1                            # a wrong price or a reveal before 120 is `refused: law-denied: …`
mini> market settle fish                   # from height 140: fills by price, then by who bid first
mini> submit settle-fish
mini> law show fish                        # the market's law, in the one-line grammar
```
a bid you never reveal fills nothing. there is no deposit yet, so not revealing costs nothing:
markets here are for friends, not for strangers who might bid and walk away.

## a librarian in a room

a room's founder can bring in the node's Hermes, an agent that holds only what it is given and
pays for each thing it writes from a budget the founder funds:

```
mini> summon lab as librarian --budget 100   # founder: Hermes joins lab's roster with 100 credit
mini> ask lab what changed since 48          # a say addressed to Hermes; it answers in its stream
mini> topup lab 50                           # its budget ran out: it said so, and stopped
mini> dismiss lab                            # founder: its grants are revoked, the rest comes back
```
the librarian links every document in the room from `lab-index`, writes a digest of what was
said into `lab-digest`, and answers "since" questions from the room's signed history. its
instructions are a document in the room, `lab-hermes-librarian`: you can read it, the founder
can edit it. each write it makes costs the room's `hermes/turn` price (`tariff lab`) plus the
fee, paid into the room's till; when its account can't pay, the Host refuses the turn and Hermes
says "out of budget" in its stream. it can't write anything it holds no grant on: ask it to
edit your document and the Host refuses it.

## how things end

stdout is the answer. when a verb fails, stderr's last line starts with who decided:

| exit | first word | meaning |
|---|---|---|
| 0 | | done |
| 1 | `error:` | the client stopped; the Host wasn't asked or didn't answer |
| 2 | `usage:` | the line didn't parse (`help VERB`) |
| 3 | `refused:` | the Host said no, and says why (below) |
| 4 | `undecided:` | the Host didn't settle it; `lookup ID` asks again |

the reason after `refused:`:
- `no-grant`: nothing you hold covers that resource and that operation.
- `unknown-key`: this key isn't enrolled (yet, or since the last reset).
- `law-denied`: the resource's current law says no (see the lock above).
- `revoked`: the grant you used, or one it came from, was revoked.
- `stale-root`: you signed against a state that has since moved; do it again.
- `bad-signature`: the signature didn't verify for that key and that exact request.
- `malformed`: the request didn't decode, or didn't fit its operation.
- `undisclosed`: a refusal before you proved who you are, or of a write at admission: on purpose
  it names nothing on your channel (the operator's log names it).

(rarer ones exist too, like `outside-validity`. refused frames are kept under `refusals/`.)

## what not to expect yet

- Numbered fields and one scalar action per `invoke`; laws may be written in the law
  grammar or JSON. Jobs run Nock programs, and each check reruns the program.
  Room weeks, chat and document editing are available; quote ranges name published
  lines, not spans within a line. IDs are write-once: pick a new one per request.
  `help guide` prints this guide. No uptime promises.

## reaching me

telegram @emberian, or ember@lunar.town. paste the whole `refused:`/`error:` block,
because it holds the Host's own decoding.

## what's planned

this is why you'd come back, with no dates promised: **streams** (chat) inside rooms, **laws in a one-line
grammar** instead of JSON, Hermes as a **game master** and as a **runner** you hand a program,
**paying with $DREGG** for a room's week (a few dollars), and
eventually **a MUD** built from the same pieces.

thank you for poking at it early. (｡◕‿◕｡)
