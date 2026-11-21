# demo-seed: initial deployment data

`seed.sh` populates a fresh demo box before enrollment opens. It runs once as root and executes
every state transition through `mini-shell-ssh` under `box`, `sage`, or `public`, producing
admitted, receipted turns in the Store. Source texts live in `data/`.

## Where it runs

Run after genesis, `public` enrollment (`/etc/mini/public-subject` exists), provisioning of `box`
and `sage`, and `mini apps bootstrap`:

    sudo deploy/demo-seed/seed.sh

Requires `/usr/local/lib/mini/infra/lib.sh` (`C`, `NODE`, `S`, `LIB`, `TENANT_GROUP`,
`TENANCY=split`), `jq`, `curl`, and `setpriv`. Optional environment overrides: `SEED_HOST`
(default `box`), `SEED_GUEST` (default `sage`), `SEED_HERMES_BUDGET` (default `100`), `TALLY_SRC`
(default `$C/world/activity/Tally.obend`).

## Frame prerequisites

- Hosted member `box`: sponsor account with credit for `bend` and `summon`. Owns the seeded
  documents, rooms, board, story, and Sandstorm grains.
- Hosted member `sage`: second participant account (`mini-reenroll sage`, provisioned and
  initialized).
- Hosted reader `public` and `/etc/mini/public-subject`. `seed.sh` ensures `/etc/mini/house-publications`
  binds `welcome` and `operations` to `box`.
- Hermes resident installed for `lobby` via `deploy/hermes/demo/install-hermes`.
- Door config pointing new enrollments at `lobby` and `tale`, and `/etc/mini/front-doc` set to
  `welcome`.

## Seeded state

- **Documents** (published to `public` with `observe` per-request bytes from `public-read-request-bytes`):
  `welcome`, `what-is-mini`, `a-refusal-explains-itself`, `the-lost-reply`,
  `the-lamplighters-note`, `house-rules`, `field-notes`.
  - Headings, bold, italic, code, and cross-document `link` marks are applied via `doc mark`.
  - Marginalia comments are attached via `doc annotate`.
  - `welcome` links to all six companion documents, transcludes `what-is-mini` lines 2..4 live,
    and appends the public `-www` URL of the `reveal.js` deck when available.
- **Rooms**:
  - `lobby`: founded by `box`, joined by `sage`, with Hermes summoned as `librarian` (budget 100)
    and initial signed turns.
  - `operations`: founded by `box`, joined by `sage` and `public` (`--verbs observe`), with
    signed checkpoint, backup, and certifier turns so `/` and `/room/operations` render live
    operational history immediately.
- **Story `tale`**: created from the built-in `tale` generator under its sealed law with `sage`
  as GM and the opening scene narrated.
- **Objective Bend `tally`**: published from `world/activity/Tally.obend` and executed on
  `lobby-tally`.
- **Delegation and refusal**:
  - `field-notes` is delegated `observe,mutate` to `sage`, who appends a verified note (`sage-note`)
    and annotates it.
  - `house-rules` is delegated `observe` only to `sage`; `sage-overstep` attempts an append and
    records a receipted refusal (exit code 3).
- **Kanban `board`**: created via `board new board`, delegated `observe,mutate` to `sage`,
  populated with task 0 (`todo` -> `doing` -> `done`, taken by `box`) and task 1 (`todo` ->
  `doing`, taken by `sage`), and published to `public` so `/board` and `/board/board` render
  active tasks.
- **Grains**: EtherCalc (`lobby-tally` CSV), Etherpad (`welcome` pad), and `reveal.js markdown decks`
  (published on its `-www` origin).

## Idempotence

Each step inspects existing state before acting (`doc show --json`, `history all`, `chat rooms`,
`story list`, `bend show`, `apps list`) and logs `seed: ok|skip|FAIL <what>`. Re-running skips
completed steps and retries any failed step.
