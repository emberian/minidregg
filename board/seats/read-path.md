# Seat: read-path

Agent: none (handed off 2026-11-01 02:30Z at ember's wind-down; editing passes to another agent). Last Claude seat:
a31482e50a323ff17. Earlier: ad74bb6d4410b48f3, before it the exorcist a97dba51f72535cb9 (`cv show <id>` for any of them).
Mac worktree: /Users/ember/dev/minidregg-lanes/exorcism, detached on `main`, clean (untracked target-exo*/ are
cargo target dirs). Commit by path, `git pull --rebase origin main`, push `HEAD:main`.
Owns: the Host's read and query ops (op 4 challenge, op 5 signed read, the read half of op 144), the codec resident's
read inspections, the client's read path (`Flow::query`, `query_retained`, `signed_view`, `read_scratch`, the read
file bus `mini_sdk::attempt`), `doc show`/`doc history` rendering, signature admission on the read side
(Compiler/CredentialSignatureAdmission, Kernel/CredentialSignedEnvelopeController), and, after host-execution's Host
side of KN2 2b, porting ClientConsentCore/ConsentAnchor onto the light `Opening`.
Quest: a warm signed read toward about 1 ms; no read grows with history or with the document (law 17).

## Landed (all on `main`)

- c4a1e4cf4 (2026-11-01, member-side read and approved it): a document append in `propose` decodes its document from
  propose's own signed read (`document_actions(.., read: Option<&Attempt>, ..)`, `read_document` over that read's
  `view.bin`) instead of a second signed read through `host_document`. The Host is read once per append, and the runs
  extended are those of the root the command pins. `cargo check --tests` was clean; the change is not measured yet.
- 14f9cbb29: op 5's opening cache picks its candidate by the cell root and compares bytes only for that one; the reply
  frame is written without a copy. Lane-check green; not measured.
- 56344846a, 8cbe36d62 (ops 4 and 5 on the light opening), a128a7497, 143caf2fc and earlier work (docs/EXORCISM.md, git log).
- Measured 2026-10-31 on persvati (warm `doc show`, Host CPU per read): before a128a7497+143caf2fc 1.71/1.55 ms, after
  1.33/1.35 ms (about 18%). 8cbe36d62 is within noise warm; its gain is the first read after a start.

No wip branches: nothing is unfinished in code.

## What an append costs, and why (the finding to carry forward)

he-births' flatness bench (scripts/perf/flatness-bench.py: fixed 42-byte appends to one document; propose CPU =
Host process tree): propose went from 14 to 61 ms over 100 appends (profiles hbox:/home/hbox/hx-births/
{p-base-early,p-base-late,inc-early,inc-late}.txt, compare with cmp.py there). Before c4a1e4cf4 the append read the
document twice. What remains is O(document) by the content format, not by the read code:
- A content cell's root is a flat salted root (Compiler/StoreCodec.lean `saltedRoot`, `leaves`): every entry's salt is
  KMAC256 under the cell's blinding key, and the blinding ratchet (K-HIDE-ROTATE, `ratchetTag`) re-keys that key at
  every write. So every write re-salts and re-hashes every entry (`physicalRoot` 9.7% -> 15% across the bench), and no
  prepared opening carries from one revision to the next (`Entry.prepare` in Kernel/NativeObservationOpeningCache.lean
  is necessarily a miss on the first read of each new revision).
- So a narrower op 5 view (`.documentTail`: root element, tail line, runs ending there) would cut the read's encode, but
  the read's opening and the write stay O(document) until the format changes. This is a decision for root and privacy:
  per-entry salts that are not re-keyed on every write leak which hidden entries did not change, which is the trade
  the ratchet was chosen to avoid. RULINGS defers blinded kinds to epoch b (the ZK selective opening).
- Constant factor available now: the write already computes every new salt and leaf. Handing them to the opening cache
  (through the Materialized Aux cache, Theory/CellStateAux.lean, the KeptCell ruling) would make the first read after
  a write skip `Entry.prepare`. That halves the hashing per append; it does not make appends flat.
- The client also scans the whole page for an append (`holds_sealed`, `refresh_document_guards`, `cell_storage` in
  native/resource-client/src/workspace.rs). A narrow view needs those answered too. member-side (ab7b4fe7fb687e0ca)
  offered to make the client ask for any narrower shape the read side defines.

## Next, in order

1. **Measure c4a1e4cf4 and 14f9cbb29** with the flatness bench. Plan, not started (the build was stopped at the
   wind-down, during `lane-tree native`'s one-time package copy): on hbox, `lane-tree acquire read-path origin/main`,
   `scripts/pipeline/native-loop read-path BASE rp-host` with BASE a builder candidate older than 14f9cbb29
   (/home/hbox/lanes/integ/candidates/467e698ef56f...), then `LANE_DIR=/home/hbox/pool/lanes/read-path swarm-build
   deploy/candidate/lane-build.sh rust --crate resource-client` and `lane-build.sh overlay BASE
   $LANE_DIR/candidates rp-hostclient host consent mini miniLine`. The script that does this is
   hbox:/home/hbox/pool/lanes/read-path/build1.sh (detached with a PID file). That gives base / +Host / +Host+client.
   Copy them to persvati (`/home/ember/mdpool/candidate-relocate DIR` after rsync) and run
   `flatness-bench.py --bin C/bin --root FRESH --src SRC --n 100 --lo 10` on each. The Host overlay carries everything
   on main since 467e698ef (including he-births' 462919a4), so step 1 -> 2 is not 14f9cbb29 alone; step 2 -> 3 is
   c4a1e4cf4 alone.
2. **Measure R1** (store-retained a9b54e85e4a194b91, 49cf4f2d2): main against main with 49cf4f2d2 reverted, the same way.
3. **Bring root the append-format decision** above, with the measured numbers from 1.
4. **Op 5 `capabilityEvidenceChecked`**: 3.9% of a warm read in the hbox profile (/ci/exo/hp.stacks.txt, tally with
   /ci/exo/sub.py), 2.8% of it `storedCapabilityDigest` (encode + cSHAKE256), about 50 us. The retained form keeps
   the digest with the session's light opening, typed by it, in the pattern of R1's `RetainedChallenges`
   (Kernel/NativeObservationController.lean: `find` returns the value with its equation). store-retained measured 19.6%
   on an L0 Host, which is a different profile; re-measure before choosing.
5. **KN2 2b consent**: port `ClientConsentCore.verifyInitial`/`ConsentAnchor.resume` onto the light `Opening`, after
   host-execution's Host side. Cold first read and restart are the full Store open until then (about 4.3 ms per record).
6. Remaining op 5 terms: `queryResultUsing` 8%, codec `challengeJson` 10%, GMP `Nat` churn in `StreamCodec`.
7. "Reads keep nothing per read" (RULINGS): a read still appends a read-journal line, rewrites seen/NAME.json when the
   world moved, and moves a refused read into attempts/. Decide each against the ruling.
8. Client twins: `query_batch_once` (native/resource-client/src/main.rs) and participant_enrollment's observation
   hand-roll `Flow::observe`; fold them onto `Flow` over a memory attempt.

## Open reds

None owned by this seat in board/REDS.md at handoff.

## Seams

- member-side ab7b4fe7fb687e0ca: owns workspace.rs (the client side of an append).
- host-execution (see board/seats/host-execution.md for its id) and he-births ac49ca4075452034f: KN2 2b, `loadTarget`.
- store-retained a9b54e85e4a194b91: R1. privacy (board/seats/privacy.md): KeptCell / Aux cache, the salt trade.
- build-loop (board/seats/build-loop.md): hbox pool, builder, persvati.

## Box state at handoff

- **hbox**: no pool tree held (t10 released; its saved patch /home/hbox/pool/saved/t10-read-path-20261101T022047Z.patch
  is empty). Build stopped by its PID file (log /home/hbox/pool/lanes/read-path/stop.log). World /ci/exo/w8 stopped by
  its PID files and removed (976 MB; log /ci/exo/w8-stop.log). Kept: /ci/exo drivers and profiles, the Rust clone
  /home/hbox/lanes/exorcism (no target), overlay /home/hbox/pool/lanes/exorcism/candidates/7f367c3dc267 (unused).
- **persvati**: no world running. Worlds after/before3/nolight were stopped with `jworld-scratch.sh down` and removed
  (2.1 GB), and candidates rp/before3 and rp/nolight were removed (1.3 GB). Kept: /home/ember/mdpool/candidates/rp/base,
  drivers /home/ember/mdpool/rp/{up.sh,hc.sh,reenroll-debug}, infra copy rp/infra-3ab3a69, Lean tree
  /home/ember/mdpool/lanes/read-path.
- **dregg-build2**: obend's; nothing of this seat runs there.
