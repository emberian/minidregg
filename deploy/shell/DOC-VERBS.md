# `doc` lines in the shell: the element tree, marks and rendering

These are the `mini shell` lines for the document verbs that the k-element-tree, k-transclude,
k-doc-index and k-marks lanes and P-DOC-RENDER added as `mini workspace` actions. Each line is
exactly **one** workspace action. The shell supplies `--dir WORKSPACE` and spells nothing else.
The parser is `native/resource-client/src/shell/doc_render.rs` (`doc_flags`), and its tests pin
every row below.

The `"doc"` arm of `native/resource-client/src/shell.rs` routes every verb below through
`doc_flags` (`mod doc_render`), passing `insert`'s TEXT through `text_argument` so that `@FILE`
works, with `--dir` prepended. `doc new`, `append`, `edit`, `annotate`, `link` and `push`
spell a proposal request or name a session file and stay in `shell.rs`.

| shell line | workspace action | prints |
|---|---|---|
| `doc show NAME` | `--action doc-show --name NAME` | the text rendering (notation below) |
| `doc show NAME --raw` | `… --format raw` | the document's own live atoms, byte-exact, one per line |
| `doc show NAME --json` | `… --format json` | the `Rendered` struct: rows + `line`, `depth`, `text`, `rendered`, `annotations`, `transcluded`; `outline`; `text` |
| `doc show NAME --html` | `… --format html` | the same structure as semantic HTML, with classes and no CSS; `mini web`'s document is these bytes |
| `doc show NAME --at H [--raw\|--json\|--html]` | `… --at H` | the document as it stood at height H, under your grant as it stood then (`refused: no-grant` otherwise) |
| `doc history NAME [--json\|--html]` | `--action doc-history --name NAME [--format …]` | one row per write: height, subject, transaction, its changes where your grant stood |
| `doc diff NAME H1 H2 [--json\|--html]` | `--action doc-diff --name NAME --from H1 --to H2 [--format …]` | `+ E`, `- E`, `~ E a -> b`, `moved E: after X -> after Y` |
| `doc pull NAME` | `--action doc-pull --name NAME` | the live lines, bytes exact (a transclusion: `⟦transclusion T⟧`) |
| `doc push ID NAME @FILE\|@-` | `--action doc-push …` | the actions it proposed; a stale line is refused by line |
| `doc annotate ID NAME LINE TEXT\|@FILE` | `propose` (payload `document`: `annotate`) | — (then `submit ID`) |
| `doc range NAME FROM TO` | `--action doc-range --name NAME --from FROM --to TO` | `workspace range: RUN` (stderr): lines FROM..TO published as one run |
| `doc outline NAME` | `--action doc-outline --name NAME` | the heading lines, `N  text`, indented two spaces per depth |
| `doc mark NAME LINE KIND` | `--action mark --name NAME --line LINE --kind KIND` | `workspace mark: ID` (stderr) |
| `doc mark NAME LINE link TARGET` | `… --kind link --to TARGET` | also `workspace mark link: ID` |
| `doc unmark NAME MARK` | `--action unmark --name NAME --mark MARK` | — |
| `doc unmark NAME LINE KIND` | `--action unmark --name NAME --line LINE --kind KIND` | refuses with the ids when the line has several marks of that kind |
| `doc insert NAME N TEXT\|@FILE` | `--action doc-insert --name NAME --at N --text TEXT` | — |
| `doc move NAME FROM TO` | `--action doc-move --name NAME --from FROM --to TO` | — |
| `doc remove NAME N` | `--action doc-remove --name NAME --line N` | — |
| `doc transclude NAME SOURCE FROM TO [snapshot\|live] [at N]` | `--action transclude --name NAME --source SOURCE --from-line FROM --to-line TO [--mode M] [--at N]` | `workspace transclusion: ID` |
| `doc transclusions NAME` | `--action transclusions --name NAME` | every transclusion, as JSON with `text` |
| `doc follow NAME T` | `--action follow --name NAME --transclusion T` | that one, re-read now; refused when you hold no read of its source |
| `doc links NAME` / `doc backlinks NAME` | `--action doc-links` / `doc-backlinks` | the Host's link index; each backlink is followed by `    line N: <rendered>`, the referencing line as you read it |

**Numbers.** `LINE`, `N`, `FROM` and `TO` are **live line numbers**, the ones `doc show` prints
(in `transclude`, the SOURCE's, which must lie in one published range: `doc range`). A struck
line shows `-` and has no number. `H`, `MARK` and `T` are decimals. A zero, a word, or a missing argument is a usage error, and nothing is sent.

**Kinds.** `bold italic code heading link`. Any other kind is refused by name before sending
(`unknownKind: underline (expected bold, italic, code, heading or link)`), the same text the Host uses.

## The notation `doc show` prints

```
  1  # Docuverse
  2  **bold words**
     ↳ you (fresh): check this
  3  _slanted_
  4  `mini serve`
  5  [see the target](→ rtarget)
     ↳ subject 1234… (fresh): who wrote this?
  -  ~~gone soon~~
  6  ⟨from rsrc lines 2..3, snapshot@31⟩
     │ source two
     │ source three
  7  ~~**changed**~~
```

| what | notation |
|---|---|
| bold / italic / code | `**t**` / `_t_` / `` `t` `` (applied innermost first: code, italic, bold, link, heading) |
| heading | `# t`, with one `#` per tree depth (`##` inside a section) |
| link mark | `[t](→ NAME)` (your name for the target), `[t](→ doc:ID)` if you have none, `[t](→ ?)` if the link was retired |
| stale mark | that kind's decoration in `~~…~~`. A kind is struck only when **every** mark of that kind on the line is stale |
| struck line | `  -  ~~text~~`, with no number |
| section | `  §`, indented by depth |
| transclusion | `⟨from DOC lines a..b, snapshot@H⟩`, `⟨… live⟩` or `⟨… live, revised⟩`, then `     │ line` for each line |
| not readable | `[transclusion: K atoms of DOC, not readable by you]` |
| object atom | `[object SCHEMA 12 KB]`; a non-UTF-8 text atom shows as `[binary 3 B]` |
| annotation | `     ↳ AUTHOR (fresh\|stale): body`, or `→ NAME` for a reference body |

The notation is **lossy by design**. `**two**` does not say how many bold marks the line holds,
and a body that contains `**` reads the same as a mark. Nothing parses the notation back into a
document. `--raw` is the byte-exact form.
