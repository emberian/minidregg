# Seat: read-path

Agent: (the next read-path seat writes its id here). Previous: ad74bb6d4410b48f3 (the exorcist a97dba51f72535cb9,
distilled once), stopped 2026-10-31 at about 470K tokens; this file is its whole continuation.
Mac worktree: /Users/ember/dev/minidregg-lanes/exorcism, detached on `main` (commit by path, `git pull --rebase`,
push `HEAD:main`; keep the tree clean: an uncommitted Lean change blocks the rebase, so park it as a patch file).
Owns: the Host's read and query ops (op 4 challenge, op 5 signed read, the read half of op 144), the codec resident's
read inspections, the client's read path (`Flow::query`, `query_retained`, `signed_view`, `read_scratch`, the read
file bus `mini_sdk::attempt`), `doc show`/`doc history` rendering, and signature admission
(Compiler/CredentialSignatureAdmission, Kernel/CredentialSignedEnvelopeController) on the read side.
Quest: a warm signed read toward ~1 ms, widest costs first; no read grows with history or with the document.

## Where a signed read stands (persvati, quiet, 2026-10-31)

Warm `doc show` of member-1, worlds from one source (main 27f85e89 + member-side's 86c9dbddb on candidate 76511e768),
2 runs of 6 alternated rounds of 300 (`/home/ember/mdpool/rp/hc.sh N ROUNDS WORLD...`; Host CPU from /proc, 10 ms ticks):

| world | Host CPU per read |
|---|---|
| `before3` (a128a7497, 143caf2fc, 8cbe36d62 reverted) | 1.71 / 1.55 ms |
| `nolight` (8cbe36d62 reverted) | 1.33 / 1.35 ms |
| `after` | 1.54 / 1.30 ms |

a128a7497 + 143caf2fc: about 0.3 ms (18%) of Host CPU per read. 8cbe36d62 (light opening): within noise warm; its gain is
the first read after a start (no full Store open), not visible at these worlds' height. End to end 11.3 ms wall per
`doc show` including the driver's process starts; resident + consent + codec about 4.1 ms CPU. On hbox (E-cores, load)
the same read was about 6.5 ms Host CPU.

## Landed (all on `main`)

- 14f9cbb29: op 5's opening cache picks its candidate by the cell root and compares bytes only for it (was: the whole
  cell's bytes against each of 16 entries, after encoding the cell twice); the reply frame is written without a copy.
  From he-births' flatness profile (propose's read 14 -> 61 ms over 100 appends). Lane-check green; not yet measured.
- 56344846a: `GrantPlan`'s constructor public (TokenCensus refused the private one).
- 8cbe36d62: ops 4 and 5 on the light opening (`challengeWireOn` over any ground, `queryWireLight`, `rememberLight`);
  history, `at h` and batch reads still open the full image (`sessionFull`). Op 4's theorems restated over any ground.
- a128a7497: signature admission hands the controller its state and registry as values (`prepareDecoded`,
  `@[csimp] prepare_eq_fast`), the envelope decoded once, `registryDigest` seven bytes per big multiplication
  (`@[csimp] registryDigest_eq_fast`).
- 143caf2fc: op 5 works out each grant's selection, request and header once (`GrantPlan`, `challengePlanned`,
  `challengePlanned_exact`).
- Earlier (numbers in docs/EXORCISM.md and git): 697d8dd4f seen snapshot not rewritten; dde0f4463 memory attempt asks
  the disk nothing; 56d65ae3c the read file bus; 837c3f457 `read_scratch::retain`; 478f170ab lazy reference names;
  3822c09f2 + d843f2ef6 `mini-line` is the ssh forced command; bc17cef1b/7e6850892 one-decode codec view; Lean
  47b7cb2e1, c763e3ead, 975491262.
- Others' work on this path: store-retained R1 49cf4f2d2 (op 4's planned challenge kept for op 5 in `Session.observed`,
  typed by the light opening, dropped on a head move; `authorizeRetained_eq`); host-execution 2b slice 1 4fb012263
  (session opens light only); member-side 86c9dbddb (consent refresh red from ed875b899).

## Next, widest first

1. **Append reads the whole document, twice (law 17).** he-births' flatness bench: propose CPU 14 -> 61 ms over 100
   fixed 42-byte appends (/ci/f-467e69/submit.log on hbox; profiles hbox:/home/hbox/hx-births/p-base-{early,late}.txt).
   The client's `document_actions` (native/resource-client/src/workspace.rs ~5749, member-side's file) fetches the
   signed resource view once for `content_page`/the signed version fields, then `host_document` (~2142) fetches a second
   signed view and decodes it whole (`view-document`) for three things only: the root element exists
   (`no_document_refusal`), the last live line of `order` (`runs_at_tail` ~5716: the last unstruck atom or an embed),
   and the ids of the runs ending at that atom (each gets an `insertRun`). An append needs a bounded answer: storage
   kind content, the cell's current root/version, the root element id, the tail line, the runs at the tail.
   Design (agree with member-side ab7b4fe7fb687e0ca before writing): a query view `.documentTail` in op 5, answered
   from the authorized cell like `resourceAnswer` but returning only those fields, its statement relating it to
   `documentJson` of the full view (the tail of `order`, the runs ending there); the client asks it once, under the
   same signature, instead of two whole views. `push`, `edit`, `annotate` stay O(document) by meaning.
   Also O(document) per revision on the Host today: `Entry.prepare` builds every entry's opening for each new
   revision. A carried-forward opening (prepared entries kept by entry key across revisions, only changed entries
   prepared) is the retained form; check first whether the opening's salt is per entry or per write ratchet (if it
   changes for every entry on every write, nothing carries).
2. **Measure R1 (49cf4f2d2) and 14f9cbb29.** Build on hbox's pool (dregg-build2 is obend's now): an overlay of main with
   49cf4f2d2 reverted against main, on a builder candidate from hbox (`/home/hbox/lanes/integ/candidates/<sha>` or
   build-loop's announcement); copy to persvati with `candidate-relocate`, worlds with `/home/ember/mdpool/rp/up.sh
   CANDIDATE RUN_DIR PORT`, compare with `hc.sh`. store-retained wants the number. R1's find is a linear scan of at most
   32 held challenges (intent + signature comparison).
3. **Op 5: `capabilityEvidenceChecked`** (19.6% of an L0 Host's read profile, store-retained's; 3.9% + `loadPolicy` 4.6%
   in mine). Per read it re-derives the stored capability's digest (`storedCapabilityDigest`: encode + cSHAKE256), and
   the membership, issuer and non-revocation checks for the capability, its ancestors and channels. Retained form: the
   digest kept with the authority cell's version (likely through privacy's KeptCell / Materialized Aux cache, ask
   privacy a3f7fce75cd3e4e49), and the policy graph loaded once per authority root. `WorldKindLawDependencies.loadTarget`
   re-hashing the target per call is he-births' (roots carried by the directory).
4. **Cold first read and restart (KN2 2b).** Both were the full Store open (`loadChained`, about 4.3 ms per record;
   1.1 s at height 256). Host side: host-execution leads (slice 1 landed). Mine after it: port
   `ClientConsentCore.verifyInitial`/`ConsentAnchor.resume` onto the light `Opening` (start at the checkpoint; the
   anchor's chain from that entry's MAC-verified tag); member-side stays out of those until then.
5. **Remaining op 5 terms** (hbox profile, before the landed fixes): the intent signature verified in op 4 and op 5
   (R1 may cover); `queryResultUsing` 8%; codec `challengeJson` 10% and GMP `Nat` churn in `StreamCodec`.
6. **"Reads keep nothing per read"** (RULINGS): a read still appends a read-journal line, rewrites seen/NAME.json when
   the world moved, and a refused read moves into attempts/. Decide each against the ruling.
7. Client twins on files: `query_batch_once` and participant_enrollment's observation hand-roll `Flow::observe`;
   fold onto `Flow` over a memory attempt. Resident statx 44 per read (pinned config 16, Host image 10).

## Seams

- member-side ab7b4fe7fb687e0ca: the client (workspace.rs: the append tail read), consent cost per read.
- host-execution a24974e84d3c540d1 and its births delegate he-births ac49ca4075452034f: KN2 2b, the session, the
  directory carrying roots, `loadTarget`.
- store-retained a9b54e85e4a194b91: R1, the reference-name index over WORKSPACE/refs (keyed per file, not on the
  directory stamp).
- build-loop a6c58cb72b0764dbb: hbox pool and builder, persvati, `native-loop`.
- privacy a3f7fce75cd3e4e49: KeptCell for item 3.
- infra aa72653a8ce442178: deletes edge/mini/shell/mini-shell-ssh once no supported candidate lacks bin/mini-line.

## Boxes, worlds, tools

- **Build:** hbox pool (`ssh hbox; . /home/hbox/pool/pool.env; t=$(/home/hbox/pool/bin/lane-tree acquire read-path
  origin/main)`; `scripts/pipeline/lane-check FILE...`; native: `LANE_POOL_ENV=/home/hbox/pool/pool.env
  scripts/pipeline/native-loop SEAT BASE LABEL` from the tree, detached with a PID file; release when done). Every
  build under swarm-build. hbox / about 41 GB free (40 GB is the warning line).
- **Measure:** persvati (`ssh persvati-remote`, no perf for users: /proc ticks). My worlds there, each stopped by
  `jworld-scratch.sh down RUN_DIR` (its PID files) before removal: /home/ember/mdpool/rp/w/{after,before3,nolight}
  (ports 22702-22704) on candidates /home/ember/mdpool/candidates/rp/{base,before3,nolight} and member-side's
  /home/ember/mdpool/lanes/cand/93b31c1c33d6 (after). Infra copy /home/ember/mdpool/rp/infra-3ab3a69; drivers
  /home/ember/mdpool/rp/{up.sh,hc.sh,reenroll-debug}. Lean checks also work in persvati:/home/ember/mdpool/lanes/read-path
  (packages shared with the seed; `export PATH=$HOME/.elan/bin:$PATH`).
- **hbox:** world /ci/exo/w8 (acc7cfa03 overlay, kept), drivers /ci/exo/{tc,rc,sc,fx,hp,wr}.sh, Host profiles
  /ci/exo/hp.stacks.txt with tallies /ci/exo/{stk,ph,sub}.py and symbols via /ci/exo/symfs; the Rust clone
  /home/hbox/lanes/exorcism (target removed; holds applied patches already on main); overlay
  /home/hbox/pool/lanes/exorcism/candidates/7f367c3dc267 (143caf2fc on batch 9, unused).
- **dregg-build2:** obend's now; nothing of this seat runs there (my overlays 6c2fc1a1bc53/f4467a28bd9c stay in its
  /srv/pool/lanes, copies are on persvati).
- Install each build into a NEW directory: `cp` onto a binary a resident runs fails with ETXTBSY.
