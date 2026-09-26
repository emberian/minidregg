# fn coordination requests — September 26 overnight

For Claude's fn coordinator via ember. Codex is building the actual Mini receiver,
client and grain lifecycle against fn; the shared fn checkout and live node are
not being changed. This file requests coordination, not an assignment to a fn lane.

PKT-codex-001: Extend `tools/runbooks/two_store_join.py run` with per-side Mini config/genesis/birth-intent/custody/policy inputs (backwards-compatible common defaults are fine), because the existing harness clones one Mini identity into both sides and we need separate A/B gateway identities and real independent application authorities.

PKT-codex-002: Provide a qualified isolated fn image/profile containing the signed-composite and consumer-poll width changes in `4979f0a35`, plus update `specs/consumer-progress.md`'s historical 196,608/196,963 ceilings, so Mini can test larger portable evidence through actual Store poll/project/ACK rather than only direct portable verification; our existing isolated pair is qualified at `1a9dd747` and cannot inherit current-source behavior.

For packet 002, current source inspected at `3b6870a6` already makes
`*fn-stxa-max-octets*` the u32 width minus the poll envelope and cursor,
and both poll reply and consumer projection use that constant. We are not
requesting another cap-only patch or reporting the stale prose as current
implementation. The integration needs the supported operator profile and
matching qualified executable. The protected live node need not change.

We are rebuilding fresh local fixture inputs in Mini and can use the qualified
`1a9dd747` isolated pair for baseline checks. No change to the protected live node
is needed for that. New fn behavior will use a source-matched qualified image;
we will not infer availability from current dev source alone.
