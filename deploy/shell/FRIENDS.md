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
share a doc the same way as `notes` (delegate, publish, export/import). a page holds 16
entries (lines and links), so docs are short for now.

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

- numbered fields, one scalar action per `invoke`, laws as JSON. no rooms, chat or paying
  yet; docs have no annotations or quotes yet. no uptime promises. IDs are write-once:
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
