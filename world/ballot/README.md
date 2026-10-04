# world/ballot — sealed-ballot (commit/reveal) vote for rooms

`SealedBallot.obend` + `preview-cohort.json` (37 rows). Evidence class: **executed in the
effect-free preview**; not native, and **not hiding** (see below).

## What it does
Three phases by height. COMMIT (`now < commitEnd`): each elector commits a digest of
(voter, vote, salt), once. REVEAL (`commitEnd <= now < revealEnd`): a committer opens its digest
with (vote, salt); only an opening that reproduces the committed digest is counted, once, as 0
(no) or 1 (yes). TALLY (`now >= revealEnd`): anyone closes the poll, once; the result is derived
from the retained openings. A commit never opened is an **abstention**. Quorum is an absolute
YES count (as in `world/collective/CollectiveAdoption.obend`); invalid terms (zero or
unattainable quorum, repeated electors, ids outside 1..999, no reveal window) never run. The
result is published with the regime label `"ballot"` (`Theory/ResearchRegime`: a ballot is never
rendered as a witness). The voter is inside the digest, so a copied commitment cannot be opened
by the copier (it abstains).

## Cohort
Honest path; refusals: mismatched vote, mismatched salt or voter, copied commitment, double
commit, double reveal, late commit, early reveal, late reveal, tally before close, double tally,
stranger commit, reveal without commit, out-of-range vote, void terms; quorum not met, nobody
revealed (all abstain), dissent does not block a quorum; the ballot law; nine activity runs
(incl. a refused publication that leaves the poll open). Teeth (each run red, logs in the lane):
skipping the digest check at reveal turns 4 rows red (mismatched vote, mismatched salt or
voter, copied commitment, an activity run); allowing a second commit turns 2 red; tallying
before the reveal window ends turns 2 red.

## What Bread had
`starbridge-apps/privacy-voting`: one-vote-per-ballot cells (WriteOnce), monotone tallies,
close once. Its README says ballot secrecy is out of scope; here the commit phase is the secrecy
mechanism. Shape from `CollectiveAdoption` (unique ballot, quorum) and `Kernel/SealedMarket`.

## Not yet native — and what is NOT claimed
* **No hiding.** Core4 has no hash primitive. `seal(voter, vote, salt) = 2*(salt*1000+voter)+vote`
  is an arithmetic stand-in: injective (binding) on ids below 1000 and votes 0/1, but the vote
  is readable from the digest. The preview shows the state machine, not secrecy. The native
  digest is the kernel's cSHAKE256 over the whole tuple (`Pred.hashEq`, as `Kernel/SealedMarket`
  does for bids); that needs a native digest atom in the language, which does not exist.
* No native route: the Plans are proposals; heights are caller-supplied `now` fields. Native
  needs the activity route with height awaits (commit end, reveal end) and the electors as
  authenticated actors (here the voter id is a field, not an authenticated subject).
* Front-end note: typed entry arguments cannot carry sum values, so the entry takes a count of
  electors with consecutive ids.
