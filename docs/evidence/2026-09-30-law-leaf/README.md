# J13: a refusal that names the clause (K-LAW-LEAF)

Run 2 of `journey.d/j13.sh`, on a fresh private Store, with a Host and a `mini`
built from branch `p-law`. 45 rows, 0 failed (`run-2/steps.tsv`,
`run-2/verdicts.txt`).

## The refusals

| step | who | line | shell `refused:` line | Host `explain` |
|---|---|---|---|---|
| 29 | B | `submit down` (2 -> 1) | `refused: law-denied: field 2 monotone (before 2, after 1) (Host refused prepare, reply byte 255)` | `field 2 monotone (before 2, after 1)` |
| 32 | B | `submit out` (2 -> 5) | `refused: law-denied: field 2 in {0,1,2} (value 5) (Host refused prepare, reply byte 255)` | `field 2 in {0,1,2} (value 5)` |
| 40 | A | `law repair board open` after `sealed` | `refused: law-denied: sealed (Host refused query, reply byte 255)` | `sealed` |
| 42 | B | `read board` after `sealed` | `refused: law-denied: sealed (Host refused query, reply byte 255)` | `sealed` |

Each refusal row checks the exit code (3), the reason and the leaf text on the
shell line, and the Host's own decoding of the retained frame (`explain`, and a
structured `leaf` with its path). The decodings are in `run-2/refusals/`; for
step 29 the Host decoded:

```
"leaf": {"path": ["1"], "text": "any [ field 2 monotone, not (verb == write) ]",
         "clause": <the committed clause as Pred JSON>, "before": "2", "after": "1"},
"explain": "field 2 monotone (before 2, after 1)"
```

Path `[1]` is clause 1 of the installed law (clause 0 is management). The
explanation drops the clause's write guard, which is false on every refused
write and so is never the reason.

## The admitted poles and controls

- B's `create 2 1` under the open law, then A installs the law written in the
  grammar (step 19; the proposal file carries the rendered Pred JSON, step 20;
  the Host parses and installs it, step 22).
- B's move 1 -> 2 after the law change is admitted and reads back 2 (steps
  23-27): the grant survives the law change.
- After both refused moves B still reads field 2 = 2 (steps 34-35).
- A installs `sealed` (`any []`, steps 36-39), then A's repair and B's read are
  refused by it.

## Where the refusal is decided

- A write is drafted by `invoke` after a read the law admits. The Host plans
  the write at `submit` (`prepare`, op 1) on the read-authorized path
  (`NativeHost.prepareAuthorizedLoaded`). There `invokeLawLeaf` evaluates each
  target's committed law on the same resolved law and projected step that
  `DeclaredResourceController.authorizeLeg` admits at submission
  (`DeclaredResourceController.lawLeaf`, `lawLeaf_fails`), and refuses with
  `law-denied` and the clause.
- A read refusal (`sealed`) is `ResourceObservationAdmission.authorizeChecked`,
  which now names the clause on the witness states of the refused admission
  (`authorizeChecked_lawDenied`, `authorizeChecked_leaf_fails`).
- Blind submission (op 2) stays uniform: `publicSubmissionOutcome` still
  answers `undisclosed` whatever the reason and clause.

## Binaries (`run-2/binaries.sha256`)

- Host `bin/minidregg-host-plaw-r1`, `b8d44306…5900`: the executable of
  `lake build Minidregg minidregg-host` on this branch (12572 jobs, green).
- `mini` `bin/mini-plaw-r1`, `a2a9c708…aae4`:
  `cargo +nightly-2026-06-21 build --release --locked`.
- Store and verifier helpers: the bake-off copies, the same as MR run 3.

Run 1 (not retained) failed its four refusal rows, as it should have: it
expected the refusal at `invoke`, which only drafts; the rows checked the leaf
text and caught the missing refusal.
