# fn coordination requests — September 26 overnight

For Claude's fn coordinator via ember. Codex is building the actual Mini receiver,
client and grain lifecycle against fn; the shared fn checkout and live node are
not being changed. This file requests coordination, not an assignment to a fn lane.

PKT-codex-001: Extend `tools/runbooks/two_store_join.py run` with per-side Mini config/genesis/birth-intent/custody/policy inputs (backwards-compatible common defaults are fine), because the existing harness clones one Mini identity into both sides and we need separate A/B gateway identities and real independent application authorities.

We are rebuilding fresh local fixture inputs in Mini and can use the qualified
`1a9dd747` isolated pair for baseline checks. No change to the protected live node
is needed for that. New fn behavior will use a source-matched qualified image;
we will not infer availability from current dev source alone.
