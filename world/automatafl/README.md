# Automatafl on Emergent Smalltalk

Two players only. `Automatafl.obend` expresses the revealed-move transition in
Objective Bend; `Run.lean` uses Mini's existing parser, elaborator, proof-producing
checker and demand machine. `oracle.rs` calls the existing Automatafl Rust
implementation. Neither adapter implements the game rules.

The shared language/object description is
[`EMERGENT-SMALLTALK.txt`](../../docs/objective-bend/EMERGENT-SMALLTALK.txt): **2,988
UTF-8 bytes**, including newlines. The game is a separate package. The capsule
describes core evaluation, a small typing contract and the host's object contract;
it is not a replacement for the `.obend` surface grammar, complete typing rules,
tariff or signed wire formats. Those are implementation interfaces, not extra game
rules. No compression, external dictionary or URL is used in its byte count.
There are also [nine compact alternatives](../../docs/objective-bend/capsules/README.md).
The current capsule separates host funding from intrinsic object identity;
the qualification below recorded the earlier 2,996-byte version at `91829303`.
Its recorded hash remains historical evidence, not a hash of the revised prose.

## The game interface

`play(w,h,board,automaton,marks,s0,t0,s1,t1)` returns
`{board,automaton,marks,status,winner}`. Indices are `y*w+x`. Board digits in base 4
are vacuum=0, attractor=1, repulsor=2, automaton=3; marks are bits. This encoding
is only a compact first-order transport representation, using unbounded Nat.
The supplied board must have exactly one automaton at the declared index, with
no digits outside its dimensions. Use dimensions >=2. Player 0 owns the two
`y=0` corners, player 1 the two `y=h-1` corners. Layout is supplied at creation.

Statuses: 0 completed, 1 conflict, 2 illegal pair (unchanged), 3 already ended.
Winner: 0 none, 1 player 0, 2 player 1. A completed result with a winner is terminal.
After a conflict both players replace their moves; accumulated marked cells are
forbidden as either endpoint. A successful round clears marks. Duplicate identical
moves coalesce; vacuum sources are allowed. Two-cycles leave pieces where they
were. Column priority is fixed; no n-player merge/rotation/freeze modes exist in
this package.

`TwoPlayer` is an explicit extension, instantiated by `fix`. This is an object of
pure methods; a durable Mini object is a different thing supplied by the host.
Pure results do not authorize writes or provide secrecy.

The model follows the no-capture, simultaneous two-player reading: a stationary
occupied destination blocks a move; a piece whose move fails remains an obstacle.
Start with both paths enabled and propagate obstruction until stable (two passes
suffice with two edges). On chains, stop at another initially occupied moving
source; traverse an empty source's onward move. This makes the failed-move
interaction explicit where the prose descriptions are underspecified.

## Cross-validation, 2026-10-08

**353 cases ran; 343 agree; 10 differ; no model invariant failed.** The reference
is the actual current, dirty `~/dev/automatafl/logic` source, configured with two
players, column priority and its default conflict mode. It is a comparison
implementation, not the definition of the rules. Its existing unrelated edits
were preserved. The older `rust/` implementation and experimental n-player
behaviors were not used.

- 172 automaton cases: named priorities/edge cases and all 81 nearest-particle
  type combinations at each of distances 1 and 2. All agree.
- 21 named pair/validation/win cases, plus 80 seeded random pairs and their 80
  player-swapped counterparts.
- Checked model conservation of each particle type, automaton location,
  preservation of the board on conflict, and player-order independence of the
  random pairs. This is finite execution evidence, not a general equivalence proof.

The ten differences have two causes in current Rust:

1. **Stationary destinations are overwritten.** On a 5x5 board, attractor at
   index 0, repulsor at 5, automaton at 12; moves `0->5` and empty `20->21`.
   The model preserves both pieces; Rust deletes the repulsor. Its occlusion loop
   excludes the endpoint and final placement overwrites it. Nine cases exhibit
   this, including their swapped forms.
2. **Failed sources remain passable.** Attractor at 0, repulsor at 2, attractor
   at 7, automaton at 12; moves `0->4` and `2->22`. The second is blocked at 7.
   Rust nevertheless moves the first through the repulsor still at 2. The model
   propagates that obstruction and leaves both pieces in place.

The [report](evidence/report.json) preserves every differing input and both
outputs. [Source hashes](evidence/sources.json) identify the dirty Rust inputs,
the model, driver and all 28 Mini modules in the runtime closure. The compact
per-case [Bend results](evidence/bend-results.jsonl) and
[Rust results](evidence/rust-results.jsonl) retain actual execution output.
Mini source base: `546c1c88`; Lean 4.30.0, independent serial build on Persvati.
The earlier checkout at `4ef4e808` produced the same 353 outcomes. The newer
front end was rebuilt and the corpus re-run after integrating upstream main.
No native admission, private hosted game or delve.town deployment is claimed.

## Reproduce

With an independently built matching Mini front end (`LEAN_PATH` holding its
oleans), Bun, Cargo and the sibling Automatafl checkout:

```sh
bun world/automatafl/check.ts prepare /tmp/automatafl-new-run ../automatafl
LEAN_NUM_THREADS=2 lean --run world/automatafl/Run.lean \
  world/automatafl/Automatafl.obend /tmp/automatafl-new-run/jobs.json \
  /tmp/automatafl-new-run/bend.jsonl
bun world/automatafl/check.ts compare /tmp/automatafl-new-run
```

`prepare` requires a new output directory and builds the Rust adapter there with
two Cargo jobs. `compare` reports disagreements separately from execution or
invariant failures; exit zero means comparison completed, **not equivalence**.
The report's `status` must be `agreement` before calling it equivalent on this
corpus. The model's input/output packing is reversible; no digest substitutes for
comparison of the complete board.

## The shared-object game

The agent-facing decomposition is three artifacts:

1. The <3 KB language/object capsule: what evaluation, objects and effects mean.
2. A pinned game package: these two-player rules and the chosen initial layout.
3. An instance descriptor: object id, code pin, player subjects, authorized
   endpoints, round/version and deadline policy; a separate host profile supplies
   sponsorship, retention and execution budgets.

Each player submits at most one move to a separately protected input slot for
the current round. Only its player can submit it; neither opponent can read it
early. The referee waits for both, reveals the pair, invokes `play`, and commits
the result against the exact state version. The object law must bind that write
to the installed package, authenticated players and round, including rejection
of duplicate or foreign submissions. Conflict opens a fresh pair of private
slots against the unchanged board and accumulated marks. A terminal winner
closes the game. An agent that loses a reply queries the original receipt; it
does not invent a new move attempt.

Private slots here require a trusted referee/host plus read protection.
Trustless simultaneous choice would instead need a genuine hiding commitment
and an agreed non-reveal policy. Core4 has no digest primitive; arithmetic
pairing is not a secrecy mechanism. Neither private ingress nor a timeout
winner is smuggled into the pure transition. They remain explicit instance
protocol decisions and receiving-path work.

The available Mini mechanisms are `ObjectRecord`/`ObjectState`, current-law
admission, atomic turns, `ObjectiveCall`, `ObjectiveSend`/`AnswerSlot`, and
checkpointed `ObjectiveActivity`. See [the object/activity contract](../../docs/OBJECTIVE-BEND-EVENTS.md).
The package still needs that concrete native adapter and receiving tests before
agents can play it as a hosted object. Plain board-game play needs no monetary
seat or wager machinery.

One additional source finding: replacing the explicit `TwoPlayer` extension
with the equivalent declared `spec` wrapper causes this package's typed packet
to be refused. A small isolated record-valued spec works, so this is not a claim
that specs generally fail. The explicit extension is checked and executed above;
the cause of the larger package's spec refusal remains to be isolated. The
[exact replacement](evidence/spec-wrapper.patch) and
[checker refusals](evidence/spec-refused.jsonl) preserve that finding.
