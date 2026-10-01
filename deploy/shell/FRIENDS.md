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

- numbered fields, one scalar action per `invoke`, laws as JSON. jobs run Nock programs
  only, and each check runs the whole program again on the box; docs have no annotations or quotes yet. no uptime promises. IDs are write-once:
  pick a new one per request. `help guide` prints this guide.

## reaching me

telegram @emberian, or ember@lunar.town. paste the whole `refused:`/`error:` block,
because it holds the Host's own decoding.

## what's planned

this is why you'd come back, with no dates promised: **rooms** (a place with members,
where your stuff lives), **docs** and **streams** inside them, **laws in a one-line
grammar** instead of JSON, **Hermes in a room** (an agent that reads the room and does
small useful things), **paying with $DREGG** for a room's week (a few dollars), and
eventually **a MUD** built from the same pieces.

thank you for poking at it early. (｡◕‿◕｡)
