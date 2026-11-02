# world/ballot — sealed-ballot (commit/reveal) vote for rooms

`SealedBallot.obend` + `preview-cohort.json` (37 rows). Evidence class: **executed in the
effect-free preview**; not hiding (see below).
Native: admitted on the activity route on candidate 0ce31391, scenario `ballot` of `native/resource-client/world-activity-admit.py`, 27/27 rows (every refusal row confirms its refusal); run `scripts/world-native-admit.sh ballot --route activity --scenario ballot --entry ballot`. Evidence: `docs/evidence/2026-10-27-world-native/ballot/` (`verdicts.txt`, `results.json`).

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

## Kernel laws and participant turns
* **Cryptographic commit-reveal (`Pred.hashEq`).** `SealedBallot.obend` declares
  `law commit_binding: new.commit == 0 or hashEq([vote], salt, commit)` alongside monotone tally
  laws (`monotone yes`, `monotone no`, `monotone abstain`). Every accepted reveal writes
  `{vote, salt, commit}` to the object state, and the kernel verifies the 32-byte
  `cSHAKE256("DREGG.PRED.HASHEQ/v2")` commitment opening via `Pred.HashEqDigest.deployed`.
* **Participant-signed turns (`deciderFor`).** When `keeper == 0n`, `deciderFor` routes each await's
  `Source.reply` decider to the next eligible voter (`nextVoter`), while a non-zero `keeper` pins a
  designated coordinator for scripted cohorts.
* Front-end note: typed entry arguments cannot carry sum values, so the entry takes a count of
  electors with consecutive ids.
