# J12 through `mini shell`: a shared document, a board, revoke (2026-09-30)

Run: `JOURNEY_GROWTH_LEVELS=10 native/resource-client/journey.sh run/manifest-psd.json run/psd3`
on persvati, from branch `p-shell-docs` at `ffcba4fe` with a clean tree. The J12 hook
(`journey.d/j12.sh`) ran on the journey's own live Store after M7. **J12 PASS, 134/134
rows ok, 617.6 s.** J12C FAIL (stub, by construction). The journey frontier is G, as
on every run of this tree (growth at level 10 only; level 1000 unmeasured), and K4
fails at field 4 (overflow), as on `product-20260930`. `journey-table.txt` is the
whole journey table.

Binaries (`manifest.json`, pinned, `inputs.sha256`):

| what | path | sha256 |
|---|---|---|
| Host | `bin/minidregg-host-psd1` (suffix build from Host.Json, 16 modules, 235 s) | `9d2add7fe09234d0dfbfee37c244baaccb213a0a8c56c6c50e8ba1040950969a` |
| mini and shell | `bin/mini-psd3` (`cargo build --release --locked`) | `f9fd2e69d2d96863df43ab2978c7d0699335e35e178ae4e95a4dd979e78435b2` |
| Store helper | product `bin/minidregg-link-sqlite-store` | `599bc4e6…fbfd` |
| verifier | product `bin/minidregg-credential-signature-verifier` | `71b8d734…b753` |

Every line in the table is typed into that friend's own `mini shell` session
(`--line`, the ssh forced command's mode; M4 already qualified the ssh entrance).
OPERATOR rows are the operator steps OPERATOR.md keeps: the custody copy (M4
Deviations 1), `provision` (step 6) and delivering the birth context (step 6). There
is no step-7 row: each friend's own `init` binds the provisioning.

Refusal rows assert exit 3, the reason and text on the first `refused:` line, and,
when the Host refused a frame, the same reason in the Host's own `inspect outcome` of
the retained frame (`refusals/WHO-*.json`). Refusals at submission come back as
the public uniform outcome `undisclosed: request refused (phase admission)` (MR's
`public_refusal_uniform`), so those three rows (97, 104, 122) can only assert that.
Each has an admitted control that differs only in the refused cause:
- 97, a reviewer's append: bob's writes to the same document were admitted (rows 73 and 75).
- 104, an edit of an append-only note: the same edit shape was admitted on `paper`, whose law is draft (rows 75 and 81).
- 122, a backwards board move: the forward moves were admitted (rows 116 and 118).

What the rendered views showed (rows 84, 86, 88, 65):

```
# doc paper: document 15795163771524832050 page root 6914…8780 at height 54 (signed read; lines are what `doc edit` takes)
  1  created-by 13071851949802628462  Alice: the first paragraph, tightened by Bob, then Alice.
  2  created-by 14591131992792524932  Bob: a second paragraph.
# 2 of 16 page entries used; created-by is the atom's creator (an edit keeps it)

# doc index: document 16456581539530926582 …
  (no lines)
link 263743731550693110446746992614528416238 -> paper (document 15795163771524832050) relation 0 created-by 14591131992792524932

# backlinks to paper (document 15795163771524832050) from the documents this workspace can read at height 54
index link 263743731550693110446746992614528416238 relation 0 created-by 14591131992792524932
# 1 backlink(s)

# delivered references (HOME/inbox); authority: discovery-only
paper	object 15795163771524832050 capability 16846642456688234317	recipient 14591131992792524932 (to me)	imported
```

Subjects: alice 13071851949802628462, bob 14591131992792524932 (from rows 5 and 16).

## What J12 can and cannot show on this store

- **Blame is by creator.** `editAtom` keeps the atom's `createdBy`
  (`Theory/HyperdocumentOperations.lean` `editAtomRecord`). So line 1 above reads
  "created-by alice" although bob and then alice rewrote it. Who edited a line needs the
  document's sibling `eventHistory` cell (PLACE §2.4). Content births do not create
  one today, and no Host read serves it (K-HISTORY-READ). Each friend's own `history`
  lists their own writes (row 90).
- **Pages are small.** A content page holds 16 entries (lines plus links). A declared
  page holds 4, and every declared object is born holding field 1 = 0
  (`NativeHostGenesis.declaredCell`). So a board has task 0 (fields 2 and 3) and task 1's
  state (field 4); task 1's owner overflows (row 126).
- **Annotate and quote cannot be expressed.** `Kernel/ContentResource.lean` `Action` has
  createDocument, createAtom, editAtom, link and createRun only. The page entry grammar
  has no transclusion or annotation records, even though the Theory has
  `TranscludePayload`/`AnnotatePayload` and their namespaces. Row 98 (J12d) and
  `j12c/quote.err` (J12C) name what is missing.
- **A write refused at admission names nothing** (see above). P-LAW's J13 ("a refusal
  that names a clause") needs the signed submitter's outcome to carry the reason.

## Rows

| n | step | who | line | expect | rc | verdict | refusal / error line (verbatim) |
|---|---|---|---|---|---|---|---|
| 1 | setup | alice | `keygen mini.key` | 0 | 0 | ok |  |
| 2 | setup | OPERATOR | `CUSTODY: copy alice's secret into the sponsor home (enroll plan+seal sign with both key...` | 0 | 0 | ok |  |
| 3 | setup | sponsor | `enroll plan alice alice.key` | 0 | 0 | ok |  |
| 4 | setup | sponsor | `enroll seal alice` | 0 | 0 | ok |  |
| 5 | setup | sponsor | `enroll submit alice` | 0 | 0 | ok |  |
| 6 | setup | check | `alice is enrolled as its own subject` | - | - | ok |  |
| 7 | setup | OPERATOR | `CUSTODY: remove the copy` | 0 | 0 | ok |  |
| 8 | setup | OPERATOR | `PROVISION (OPERATOR step 6): factory observation + a funded account owned by alice` | 0 | 0 | ok |  |
| 9 | setup | OPERATOR | `DELIVER (OPERATOR step 6): the birth context into alice's HOME/provision/` | 0 | 0 | ok |  |
| 10 | setup | alice | `init mini.key 13071851949802628462` | 0 | 0 | ok |  |
| 11 | setup | check | `alice's workspace is bound to its birth context and a session namespace` | - | - | ok |  |
| 12 | setup | bob | `keygen mini.key` | 0 | 0 | ok |  |
| 13 | setup | OPERATOR | `CUSTODY: copy bob's secret into the sponsor home (enroll plan+seal sign with both keys;...` | 0 | 0 | ok |  |
| 14 | setup | sponsor | `enroll plan bob bob.key` | 0 | 0 | ok |  |
| 15 | setup | sponsor | `enroll seal bob` | 0 | 0 | ok |  |
| 16 | setup | sponsor | `enroll submit bob` | 0 | 0 | ok |  |
| 17 | setup | check | `bob is enrolled as its own subject` | - | - | ok |  |
| 18 | setup | OPERATOR | `CUSTODY: remove the copy` | 0 | 0 | ok |  |
| 19 | setup | OPERATOR | `PROVISION (OPERATOR step 6): factory observation + a funded account owned by bob` | 0 | 0 | ok |  |
| 20 | setup | OPERATOR | `DELIVER (OPERATOR step 6): the birth context into bob's HOME/provision/` | 0 | 0 | ok |  |
| 21 | setup | bob | `init mini.key 14591131992792524932` | 0 | 0 | ok |  |
| 22 | setup | check | `bob's workspace is bound to its birth context and a session namespace` | - | - | ok |  |
| 23 | setup | rev | `keygen mini.key` | 0 | 0 | ok |  |
| 24 | setup | OPERATOR | `CUSTODY: copy rev's secret into the sponsor home (enroll plan+seal sign with both keys;...` | 0 | 0 | ok |  |
| 25 | setup | sponsor | `enroll plan rev rev.key` | 0 | 0 | ok |  |
| 26 | setup | sponsor | `enroll seal rev` | 0 | 0 | ok |  |
| 27 | setup | sponsor | `enroll submit rev` | 0 | 0 | ok |  |
| 28 | setup | check | `rev is enrolled as its own subject` | - | - | ok |  |
| 29 | setup | OPERATOR | `CUSTODY: remove the copy` | 0 | 0 | ok |  |
| 30 | setup | OPERATOR | `PROVISION (OPERATOR step 6): factory observation + a funded account owned by rev` | 0 | 0 | ok |  |
| 31 | setup | OPERATOR | `DELIVER (OPERATOR step 6): the birth context into rev's HOME/provision/` | 0 | 0 | ok |  |
| 32 | setup | rev | `init mini.key 12588663092545306355` | 0 | 0 | ok |  |
| 33 | setup | check | `rev's workspace is bound to its birth context and a session namespace` | - | - | ok |  |
| 34 | setup | eve | `keygen mini.key` | 0 | 0 | ok |  |
| 35 | setup | OPERATOR | `CUSTODY: copy eve's secret into the sponsor home (enroll plan+seal sign with both keys;...` | 0 | 0 | ok |  |
| 36 | setup | sponsor | `enroll plan eve eve.key` | 0 | 0 | ok |  |
| 37 | setup | sponsor | `enroll seal eve` | 0 | 0 | ok |  |
| 38 | setup | sponsor | `enroll submit eve` | 0 | 0 | ok |  |
| 39 | setup | check | `eve is enrolled as its own subject` | - | - | ok |  |
| 40 | setup | OPERATOR | `CUSTODY: remove the copy` | 0 | 0 | ok |  |
| 41 | setup | OPERATOR | `PROVISION (OPERATOR step 6): factory observation + a funded account owned by eve` | 0 | 0 | ok |  |
| 42 | setup | OPERATOR | `DELIVER (OPERATOR step 6): the birth context into eve's HOME/provision/` | 0 | 0 | ok |  |
| 43 | setup | eve | `init mini.key 13638194795160528636` | 0 | 0 | ok |  |
| 44 | setup | check | `eve's workspace is bound to its birth context and a session namespace` | - | - | ok |  |
| 45 | setup | early | `keygen mini.key` | 0 | 0 | ok |  |
| 46 | setup | early | `init mini.key 4242` | 1 | 1 | ok | error: init needs your provisioning at STEP/h/early/provision/birth-context.json (your sponsor writes it when they provision you); without it this workspace could never create |
| 47 | setup | check | `no workspace was made for the unprovisioned session` | - | - | ok |  |
| 48 | J12 | alice | `doc new paper` | 0 | 0 | ok |  |
| 49 | J12 | alice | `doc new index` | 0 | 0 | ok |  |
| 50 | J12 | alice | `delegate g-bob-paper paper 14591131992792524932 observe,mutate 50000` | 0 | 0 | ok |  |
| 51 | J12 | alice | `submit g-bob-paper` | 0 | 0 | ok |  |
| 52 | J12 | alice | `publish g-bob-paper` | 0 | 0 | ok |  |
| 53 | J12 | alice | `export g-bob-paper` | 0 | 0 | ok |  |
| 54 | J12 | bob | `import paper {"authority":"hint-only","capability":"16846642456688234317","kind":"objec...` | 0 | 0 | ok |  |
| 55 | J12 | alice | `delegate g-bob-index index 14591131992792524932 observe,mutate 50000` | 0 | 0 | ok |  |
| 56 | J12 | alice | `submit g-bob-index` | 0 | 0 | ok |  |
| 57 | J12 | alice | `publish g-bob-index` | 0 | 0 | ok |  |
| 58 | J12 | alice | `export g-bob-index` | 0 | 0 | ok |  |
| 59 | J12 | bob | `import index {"authority":"hint-only","capability":"18083458856010797081","kind":"objec...` | 0 | 0 | ok |  |
| 60 | J12 | alice | `delegate g-rev paper 12588663092545306355 observe 50000` | 0 | 0 | ok |  |
| 61 | J12 | alice | `submit g-rev` | 0 | 0 | ok |  |
| 62 | J12 | alice | `publish g-rev` | 0 | 0 | ok |  |
| 63 | J12 | alice | `export g-rev` | 0 | 0 | ok |  |
| 64 | J12 | rev | `import paper {"authority":"hint-only","capability":"10803648274796352903","kind":"objec...` | 0 | 0 | ok |  |
| 65 | J12 | bob | `inbox` | 0 | 0 | ok |  |
| 66 | J12 | check | `bob's inbox: paper addressed to bob, imported` | - | - | ok |  |
| 67 | J12 | alice | `doc append a1 paper 'Alice: the first paragraph.'` | 0 | 0 | ok |  |
| 68 | J12 | alice | `submit a1` | 0 | 0 | ok |  |
| 69 | J12 | alice | `doc show paper` | 0 | 0 | ok |  |
| 70 | J12 | bob | `doc show paper` | 0 | 0 | ok |  |
| 71 | J12 | check | `bob reads alice's line 1` | - | - | ok |  |
| 72 | J12 | bob | `doc append b1 paper 'Bob: a second paragraph.'` | 0 | 0 | ok |  |
| 73 | J12 | bob | `submit b1` | 0 | 0 | ok |  |
| 74 | J12 | bob | `doc edit b2 paper 1 'Alice: the first paragraph, tightened by Bob.'` | 0 | 0 | ok |  |
| 75 | J12 | bob | `submit b2` | 0 | 0 | ok |  |
| 76 | J12 | alice | `doc edit a2 paper 1 'Alice: my own rewrite.'` | 0 | 0 | ok |  |
| 77 | J12 | alice | `submit a2` | 3 | 3 | ok | refused: operation-rejected: invocation preparation: Minidregg.Kernel.DeclaredResourceController.Reject.content (Minidregg.Kernel.ContentResource.Reject.staleAtom) (phase prepare) (Host refused prepare, reply byte 255) |
| 78 | J12 | alice | `doc show paper` | 0 | 0 | ok |  |
| 79 | J12 | check | `alice rereads: line 1 is bob's edit` | - | - | ok |  |
| 80 | J12 | alice | `doc edit a3 paper 1 'Alice: the first paragraph, tightened by Bob, then Alice.'` | 0 | 0 | ok |  |
| 81 | J12 | alice | `submit a3` | 0 | 0 | ok |  |
| 82 | J12 | bob | `doc link l1 index paper` | 0 | 0 | ok |  |
| 83 | J12 | bob | `submit l1` | 0 | 0 | ok |  |
| 84 | J12 | alice | `doc show paper` | 0 | 0 | ok |  |
| 85 | J12 | check | `blame: line 1 created by alice, line 2 created by bob` | - | - | ok |  |
| 86 | J12 | alice | `doc show index` | 0 | 0 | ok |  |
| 87 | J12 | check | `index links to paper, created by bob` | - | - | ok |  |
| 88 | J12 | alice | `doc backlinks paper` | 0 | 0 | ok |  |
| 89 | J12 | check | `backlinks of paper: index's link by bob` | - | - | ok |  |
| 90 | J12 | bob | `history` | 0 | 0 | ok |  |
| 91 | J12 | check | `bob's history holds his three accepted writes` | - | - | ok |  |
| 92 | J12 | eve | `import stolen object 15795163771524832050 16846642456688234317` | 0 | 0 | ok |  |
| 93 | J12 | eve | `doc show stolen` | 3 | 3 | ok | refused: no-grant: this key holds no grant covering this target and operation (phase observation) (Host refused query, reply byte 255) |
| 94 | J12 | eve | `doc append e1 stolen 'Eve was here.'` | 3 | 3 | ok | refused: no-grant: this key holds no grant covering this target and operation (phase observation) (Host refused query, reply byte 255) |
| 95 | J12 | rev | `doc show paper` | 0 | 0 | ok |  |
| 96 | J12 | rev | `doc append r1 paper 'Reviewer: a note.'` | 0 | 0 | ok |  |
| 97 | J12 | rev | `submit r1` | 3 | 3 | ok | refused: undisclosed: request refused (phase admission) |
| 98 | J12d | rev | `doc annotate paper 1 'Reviewer: cite this.'` | 1 | 1 | ok | error: doc annotate: this store's content cell has no annotation action (Kernel/ContentResource.lean Action is createDocument, createAtom, editAtom, link, createRun; Theory/HyperdocumentOperations.lean AnnotatePayload and the annotations namespace are not in the page entry grammar); needs K-CONTENT-ACTIONS, and annotate-but-not-edit needs K-FIELDS |
| 99 | J12 | alice | `doc new log note` | 0 | 0 | ok |  |
| 100 | J12 | alice | `doc append n1 log 'Decided: we write the paper together.'` | 0 | 0 | ok |  |
| 101 | J12 | alice | `submit n1` | 0 | 0 | ok |  |
| 102 | J12 | alice | `doc show log` | 0 | 0 | ok |  |
| 103 | J12 | alice | `doc edit n2 log 1 'Decided: something else.'` | 0 | 0 | ok |  |
| 104 | J12 | alice | `submit n2` | 3 | 3 | ok | refused: undisclosed: request refused (phase admission) |
| 105 | J12 | alice | `board new tasks` | 0 | 0 | ok |  |
| 106 | J12 | alice | `delegate g-bob-tasks tasks 14591131992792524932 observe,mutate 50000` | 0 | 0 | ok |  |
| 107 | J12 | alice | `submit g-bob-tasks` | 0 | 0 | ok |  |
| 108 | J12 | alice | `publish g-bob-tasks` | 0 | 0 | ok |  |
| 109 | J12 | alice | `export g-bob-tasks` | 0 | 0 | ok |  |
| 110 | J12 | bob | `import tasks {"authority":"hint-only","capability":"10045206319151650610","kind":"objec...` | 0 | 0 | ok |  |
| 111 | J12 | alice | `board add t0 tasks 0` | 0 | 0 | ok |  |
| 112 | J12 | alice | `submit t0` | 0 | 0 | ok |  |
| 113 | J12 | bob | `board take k0 tasks 0` | 0 | 0 | ok |  |
| 114 | J12 | bob | `submit k0` | 0 | 0 | ok |  |
| 115 | J12 | bob | `board move m1 tasks 0 todo doing` | 0 | 0 | ok |  |
| 116 | J12 | bob | `submit m1` | 0 | 0 | ok |  |
| 117 | J12 | bob | `board move m2 tasks 0 doing done` | 0 | 0 | ok |  |
| 118 | J12 | bob | `submit m2` | 0 | 0 | ok |  |
| 119 | J12 | bob | `read tasks` | 0 | 0 | ok |  |
| 120 | J12 | check | `task 0 is done (field 2 = 2) and owned by bob (field 3)` | - | - | ok |  |
| 121 | J12 | bob | `board move m3 tasks 0 done todo` | 0 | 0 | ok |  |
| 122 | J12 | bob | `submit m3` | 3 | 3 | ok | refused: undisclosed: request refused (phase admission) |
| 123 | J12 | alice | `board add t1 tasks 1` | 0 | 0 | ok |  |
| 124 | J12 | alice | `submit t1` | 0 | 0 | ok |  |
| 125 | J12 | bob | `board take k1 tasks 1` | 0 | 0 | ok |  |
| 126 | J12 | bob | `submit k1` | 3 | 3 | ok | refused: operation-rejected: invocation preparation: Minidregg.Kernel.DeclaredResourceController.Reject.scalar (Minidregg.Kernel.DeclaredResourceScalar.Reject.pageMutation (Minidregg.Compiler.DeclaredEffectPageMaterializer.RejectReason.overflow)) (phase prepare) (Host refused prepare, reply byte 255) |
| 127 | J12 | alice | `revoke cut-bob paper 14591131992792524932` | 0 | 0 | ok |  |
| 128 | J12 | alice | `submit cut-bob` | 0 | 0 | ok |  |
| 129 | J12 | bob | `doc show paper` | 3 | 3 | ok | refused: revoked: the grant, one of its ancestors, or one of its channels is revoked (phase observation) (Host refused query, reply byte 255) |
| 130 | J12 | alice | `doc show paper` | 0 | 0 | ok |  |
| 131 | J12 | check | `control: alice still reads her document` | - | - | ok |  |
| 132 | J12 | bob | `help guide` | 1 | 1 | ok | error: the friends' guide is not installed at /usr/local/lib/mini/FRIENDS.md (No such file or directory (os error 2)); it is deploy/shell/FRIENDS.md in the Mini source, and ember sent you a copy |
| 133 | J12 | bob | `help` | 0 | 0 | ok |  |
| 134 | J12 | check | `help's first line is the hosted-custody banner` | - | - | ok |  |
