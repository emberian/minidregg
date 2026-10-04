# world/play: a two-party commit/reveal game

`CommitReveal.obend` is rock, paper, scissors between two players who do not trust each other,
with a stake each. Preview evidence only (effect-free preview, `preview-cohort.json`, 29 rows);
no native receipt exists for this package.

## What it does

A and B each escrow `stake`. They act in a fixed order, each within `window` heights of the
previous move: A commits, B commits, A reveals, B reveals. A commit is the digest `seal(move, salt)`.
A reveal must open its own player's digest. Refused, leaving the game exactly where it was: a move
out of turn, from a stranger, after the window, a reveal that does not open the digest, a move
outside {0,1,2}. `timeout` may be called by anyone once a window has lapsed:

- a lapse in a commit window voids the game (both stakes back);
- a lapse in A's reveal window forfeits A (the pot to B);
- a lapse in B's reveal window forfeits B (the pot to A).

B reveals last and so alone could learn the result first; refusing to reveal costs the whole
stake, never less than losing. Every settlement pays out exactly the pot, once (`potConserved`).
As in `world/bounty`, the same game is also an Activity (`play`) that yields an `await` Plan per
step and a final `disburse`; the Plans are proposals, and escrow and payout are the kernel seats'
job, not this program's.

## What Bread had

Bread's `dice` crate (verifiable randomness: `CommitReveal`, `Hybrid` with an LB-VRF key chain,
a drand beacon) and the dreggnet arcade. Its own header says commit-reveal "does NOT prevent
selective abort ... needs timeout finalization with a deterministic consequence (a follow-up)".
That follow-up is the forfeit rule here. Bread's games ran with no evidenced users.

## What is not yet native

- **The digest is a stand-in.** Core4 has no hash primitive; `seal(move, salt) = 3*salt + move` binds
  a commit to one (move, salt) but does not hide the move (`seal mod 3` is the move). The native commit
  is the kernel's cSHAKE256 opening predicate (`Pred.hashEq`, as `Kernel/SealedMarket` uses for sealed
  bids); only `seal` changes then. Until then the game demonstrates binding, turn order, timeout and
  forfeit, not secrecy.
- **No stakes move.** A seat per player (give = stake, want = pot or stake back, exit at the deadline)
  needs SEATS-NATIVE and the activity native route; here the `disburse` Plan is only data.
- **Heights are caller-supplied** (`now` in every event); natively the kernel supplies the height.
- No verifiable randomness (drand): a commit/reveal game needs none; a dice game would.

## Evidence

`bun tests/objective-bend-source/check-preview.ts world/play/preview-cohort.json OUT LEAN LEAN_PATH`
(or `scripts/check-world-cohorts.sh`): 21 closed rows (happy paths, every refusal, every timeout)
and 8 activity rows (full games, ignored illegal moves, a refused payout that waits, a stall at a
yield). Mutations that turn rows red are listed in the commit message.
