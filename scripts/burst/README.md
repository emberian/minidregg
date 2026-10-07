# scripts/burst — a burst of Mini build boxes from one entry point

Everything the burst2 boxes (2026-10-06/07) needed was applied by hand: slot files, the sccache server,
box.env, keys, the shared remote and its hbox mirror, the publisher and journey runner in tmux, package
installs, the slice cap. None of it would survive a rebuild. These scripts are that state, checked in.

| script | what |
|---|---|
| `burst-up --id ID --tip SHA --gate HOST --journeys HOST --hbox hbox --briefs ~/dev/redregg/work HOST...` | fresh Ubuntu boxes to the current state; idempotent; `--phase` for a subset |
| `remote/root.sh` | root phase on the box: disk, packages (`fuser` included), user, capnp, `swarm-build`, slice cap, **slots sized from nproc/RAM**, /srv layout |
| `remote/user.sh` | user phase: toolchains, /srv/mini at TIP, profile, pipeline scripts (from the staged checkout), sccache, box.env, REPL, **persistent units**, shared remote, SPK, briefs |
| `remote/check.sh` | one `ok`/`DIFF` row per expectation; exit = DIFF count. On a hand-built box: the behaviour diff. After burst-up: the proof |
| `cold-build.sh`, `make-warm-base.sh` | the warm base at a tip (gate box); other boxes get it by `scripts/pipeline/relay-base.sh` (a fresh box: full copy) |
| `burst-down --id ID HOST...` | collect (shared remote bundle, lane bundles + uncommitted diffs + logs, READY artifacts, journeys, slots.log, box.env, burst logs) and relay to hbox; verifies counts; **never deletes** |
| `burst-container HOST NAME PORT PUBKEY` | a fresh Ubuntu in an nspawn container on a box: the stand-in for a new box when none can be rented |
| `swarm-build` | the one source of the box binary (named scopes `swarm-<lane>-<pid>`) |
| `hbox-pull.sh`, `units/*.service` | hbox's read-only puller (timer) and the box's user units |

Keys (bounded, operational, Ember 10-07): box↔box peer keys forced to `box-peer-gate` (git fetch, read-only
rsync of /srv, `slots`, `peer-build`); the gate's mirror key accepted by the others as `rrsync /srv/artifacts`;
hbox's puller key accepted by the gate as `box-peer-gate`. No box holds a key to hbox or to anything outside
the burst. `burst-down` relays through the machine that runs it.

Nix: a flake for the toolchain (lean/elan pin, rust, bun, capnp 1.5.0, sccache, zstd, jq, rrsync) would replace
the package + toolchain half of `root.sh`/`user.sh` (~60 lines) and make two boxes bit-identical in those
inputs; it does not cover the box state (slots, units, keys, bases, remote), which is the half that was
actually lost. Cost: a day to write and pin, plus Nix on every box (a 1-2 GB store). Proposed, not blocking.
