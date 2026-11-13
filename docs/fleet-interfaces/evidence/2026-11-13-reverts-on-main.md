# nanodregg's reverts gate (GATES-30) over minidregg `main`, 2026-10-31 to 2026-11-09

**What ran.** nanodregg `gates/reverts.py` at `62f9813` (window 100), unchanged, on every non-merge
commit of minidregg `main` from `02cfb571f` (2026-10-31) to `c492c4dd3` (2026-11-09), skipping
the builder's `REDS.md` and fixture-rerecord commits: 790 commits. The gate flags a commit whose
tree restores the before-image of a hunk that one of the previous 100 landings wrote. The script
is [`reverts-probe.sh`](reverts-probe.sh); the flags are in
[`2026-11-13-reverts-flags.tsv`](2026-11-13-reverts-flags.tsv).

**Cost.** 3 min 01 s wall for 790 commits, 6 at a time on a 24-thread box at load ~8; per commit
p50 1.13 s, p95 2.67 s, max 6.10 s. Re-run from a clean checkout on a second box (32 threads, 6 at a time):
the same 9 flags over 796 commits (its date boundary takes in 6 more), per commit p50 0.22 s,
p95 0.50 s, max 1.40 s. At this repo's rate (about 80 commits a day in this window) a per-commit
gate costs well under 2 s a commit.

**Result.** 9 flags, 8 events (`01a60d40e` is the rebased twin of `98d9773c3`; `e4796e5f7`
merged the lane's original commits back under `main`).

| commit | takes back | hunks | reading |
|---|---|---|---|
| `b7d21a587` | `efbec07fb` | 9/11 | declared: subject "Revert efbec07fb" |
| `1c670cee5` | `a4b37cd28` | 2/2 | declared: subject "(reverts a4b37cd28)" |
| `7b20a1379` | `82a555e85` | 6/13 | declared: body "back to their state before 82a555e85" |
| `f54417497` | `d73a0cdea` | 1/11 | declared: body "resource-client's src/streams.rs is gone" (one implementation) |
| `8f2d63fab` | `a37e28146` | 1/3 | a move: the same lines re-added earlier in the function (subject says so); a false flag for "takes back" |
| `b7ce48271` | `df55c10a2` | 1/7 | a redescription that its subject names ("match Hummingbird hits stream") |
| `f112fa643` | `8221ced44` | 1/12 | not named; plausibly superseded by the shell pool it adds (43 min later) |
| `98d9773c3` | `d54fdf395` | 1/2 | **not named; still absent on `main`** |

**The one that looks silent.** `d54fdf395` (authored 2026-11-01 20:20) "prefer confirmed settlement
rows in prompt_outcome::audit_chain **and auto-run retry.admin in close_refused_pending**" changed
two files. `98d9773c3` (authored 20:44, committed 02:01, subject "preserve compaction quiescence,
operator audit boundary, split-tenancy continuity check, and seed.sh doc_mark idempotency")
restores the one hunk `d54fdf395` made in `native/grain-runtime/src/room_resident.rs` (its other
hunk is in `prompt_outcome.rs` and stays) byte for byte to its state before it: the `try_prompt_audit` closure and the loop that runs `retry.admin` before the second
audit are gone. The message does not mention it. At `c492c4dd3`, `try_prompt_audit` occurs 0 times
in that file (`git show origin/main:native/grain-runtime/src/room_resident.rs | grep -c try_prompt_audit`),
so `close_refused_pending` again closes a refused pending prompt without running its admin retry.
That is the GATES-30 shape (a commit from a copy of the tree that predates a landing). Whether it
was meant is the author's call.

**What this says for fleet.** On a trunk where seats commit straight to `main`, at least 1 of 790 commits
silently took back another landing's hunk and it survived a week; 4 of 8 events were declared in
prose that a gate cannot read, which is why nanodregg's `scripts/commit` asks for `--reverts C`
instead. The move in `8f2d63fab` is a false flag of the hunk-level reading.

**Not done.** No build or test of minidregg; nothing here says whether the `retry.admin` half is
needed today.
