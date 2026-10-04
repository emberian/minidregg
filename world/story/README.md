# world/story: a co-authored story

`CoAuthor.obend` is a story a crowd writes one chapter at a time. Preview evidence only
(`preview-cohort.json`, 33 rows); no native receipt exists for this package.

## What it does

Each round has a window of `window` heights. Any author may propose one passage per round and edit
their own proposal while the round is open; electors vote once each for a proposal; when the window
closes anyone may `seal`. The proposal with the most votes becomes the next chapter for good; a
tie goes to the earliest proposal (so a lone, unvoted proposal wins); a round with no proposal is
extended by a window. The losing proposals are dropped and the next round opens. After `total`
chapters the story is complete and takes no more events.

Refusals are named, not boolean: `late`, `alreadyProposed`, `notAuthor` (edit by a non-author),
`sealed` (edit of a chapter already sealed), `unknown` (an id that is in no open round, which
includes a dropped loser), `notElector`, `alreadyVoted`, `early` (seal before the window ends),
`complete`. A refused event leaves the story unchanged (`refusalChangesNothing`).

The same story is an Activity (`tell`): an `await {chapter, closes}` Plan per step and, per sealed
chapter, a `publish {chapter, author, text}` Plan; a refused publication leaves the round open for the
seal to be retried.

## What Bread had

`spween-dregg` collective mode (`collective.rs`, `vote.rs`): at each choice a poll opens, the
audience votes, the winner's turn fires and the world advances, "no operator can pick a different
branch than the crowd chose"; plus `narrator` and `interactive-fiction-demo`. Ran locally only.
Bread's branches were nodes of a compiled spween script; here the crowd authors them, and
authorship and sealing are enforced.

## What is not yet native

- Passages are opaque `String`s. Natively a passage is a hyperdocument and the winner is appended by
  the kernel; `publish` is only a Plan (data).
- The electorate is a contiguous id range `{first, count}`, not a list: a sum-typed (variant) value
  cannot be passed to an entry point today (`typedArgument` in `Compiler/ObjectiveBendElaborate.lean`
  accepts only natural, boolean, label and record), so a recursive `Voters` list could not be
  an argument of `tell`. Natively the electorate is whatever the room's membership says.
- Votes are public (no commit phase); no ResearchRegime `ballot` label on the result.
- Heights are caller-supplied; one vote per elector, no weights.
