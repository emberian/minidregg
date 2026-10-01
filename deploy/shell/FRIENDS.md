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

the hosted shell above is a convenience: your Mini key lives in your session home on the
box, so the box's operator (root and the `mini` user) could read it and sign as you. if you
would rather it never leave your machine, use **proxy mode**: you run the same `mini`
locally and the box only relays its frames (it keeps what you store, not your key).

1. get `mini` for your machine from the candidate (Linux x86-64 `bin/mini`, macOS arm64
   `bin/clients/aarch64-apple-darwin/mini`) and check its SHA-256 against `SHA256SUMS`.
2. put `Host mini-box` with your ssh key in `~/.ssh/config`, and ask me for a **proxy**
   key line (`mode=proxy`) instead of a shell one.
3. the three commands:

```
mini join --key ~/.mini/me.key
    # prints your Mini public key (64 hex): send it to me
mini --remote mini-box join --key ~/.mini/me.key --sponsor-plan offer.json --dir ~/.mini/box
    # offer.json is what i send back; you sign possession and it prints a signature: send it
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
mini> law lock notes {"type":"any","predicates":[]}    # "any of nothing": denies everything
mini> submit lock
mini> read notes                                       # refused: law-denied: …   (exit 3)
mini> law unlock notes {"type":"all","predicates":[]}  # refused: law-denied: …
```
that's the point: nobody can bypass it, not you as owner and not me. **a lock is
permanent**, so lock throwaway things. `history` lists what you did and how each attempt ended.
take a grant back with `revoke cut notes SAMS-SUBJECT`, then `submit cut`; sam's next read
is `refused: revoked`.

documents. a doc is a resource whose lines you append and edit together:
```
mini> doc new paper                       # (or `doc new log note`: append-only, edits refused)
mini> doc append p1 paper 'first paragraph'
mini> submit p1
mini> doc show paper                      # numbered lines, who created each
mini> doc edit p2 paper 1 'first paragraph, better'
mini> submit p2                           # refused if someone changed line 1 since your `doc show`
mini> doc link p3 index paper             # a link from index to paper; `doc backlinks paper` finds it
mini> board new tasks                     # tasks 0 and 1: `board add`, `board take`, `board move … todo doing`
```
share a doc the same way as `notes` (delegate, publish, export/import). a doc lives in one
content cell with no fixed size; its lines are ordered by their atom ids.

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
(`birthRefused`), while their reads keep working. you can't leave a room yourself yet
(`room leave` says so): ask its founder to kick you.

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
- `undisclosed`: a refusal before you proved who you are, so on purpose it names nothing.

(rarer ones exist too, like `outside-validity`. refused frames are kept under `refusals/`.)

## what not to expect yet

- numbered fields, one scalar action per `invoke`, laws as JSON. no paying yet; chat
  rooms are new (`help chat`); docs have no annotations or quotes yet. no uptime promises. IDs are write-once:
  pick a new one per request. `help guide` prints this guide.

## reaching me

telegram @emberian, or ember@lunar.town. paste the whole `refused:`/`error:` block,
because it holds the Host's own decoding.

## what's planned

this is why you'd come back, with no dates promised: **streams** (chat) inside rooms, **laws in a one-line
grammar** instead of JSON, **Hermes in a room** (an agent that reads the room and does
small useful things), **paying with $DREGG** for a room's week (a few dollars), and
eventually **a MUD** built from the same pieces.

thank you for poking at it early. (｡◕‿◕｡)
