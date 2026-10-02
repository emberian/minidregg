# Fresh workspace continuity

Fresh product onboarding establishes its first authenticated continuity baseline
before returning an admitted workspace to the user. The shared Rust entry points
are `workspace::init_fresh` and `workspace::complete_fresh_onboarding`.

`init_fresh` takes the existing `init` arguments followed by an exact first readable
reference (`name`, `kind`, `target`, `observeCapability`, all strings) and an optional
local verifier path. An explicit local Host supplies the default verifier; remote
workspaces require a portable local verifier. No executable is selected from PATH.
It only accepts a newly created directory and durably pins the verifier image,
source-derived deployment identity, config bytes, participant/transport binding,
and first reference before publishing the workspace manifest.

After importing that reference and making the pinned Host transport available,
`complete_fresh_onboarding(root)` performs the signed read and source-verified
op151 bootstrap. Product join/bootstrap flows call this themselves; users should
not need to discover a continuity command. Its JSON result visibly reports
`established`, `resumed`, or `verified`, with the current identity and point.
Completed calls validate and return current retained custody without another read
through the initial reference, which may have legitimately rotated or expired.

The equivalent CLI pipeline is:

```sh
mini workspace --action init ... \
  --continuity-ref '{"name":"account","kind":"account","target":"20","observeCapability":"30"}' \
  --verifier /absolute/pinned/minidregg-host
# Import the exact reference; start/connect the pinned Host transport.
mini workspace --action onboard --dir /absolute/workspace
```

`receipt-continuity.pending.json` and the manifest's `freshContinuity` enrollment
ID distinguish this path from legacy workspaces. Its states are:

- `awaiting-first-read`: ordinary reads and writes fail until onboarding finishes.
  Unexpected existing custody prevents bootstrap.
- `verified-candidate`: the exact normalized challenge, request and response have
  reached durable storage. Recovery rechecks that exact candidate with the pinned
  source verifier, then finishes anchor, settings and manifest persistence. It
  never obtains a replacement head or replaces conflicting custody.
- `complete`: the initial proof remains enrollment evidence. Ordinary advancing
  custody owns the current anchor, config, identity and verifier; explicit verifier
  replacement and verified carry transitions can update them without rewriting
  initial evidence. Missing enabled custody fails, including on repeated onboarding.

A root-level flock serializes enrollment completion; existing custody locking and
fsync/temp/rename/directory-fsync operations are reused. A crash between verified
candidate and enablement can resume. Tests exercise actual helper calls and child
process termination at persistence phases; these are process-crash checks, not
power-loss simulation.

Legacy workspaces lacking a fresh enrollment pin remain legacy. They use the
existing explicit `continuity-init` migration and cannot be reclassified by
`onboard`. Paid join owns its `init_fresh` staging hook and calls completion after
account/factory imports, before success publication. Fresh Hermes bootstrap calls
it separately for each workspace after socket readiness and before resource work.
Existing active Hermes workspaces need explicit legacy migration. Remote
`join_welcome` still needs a portable pinned verifier and a readable first reference
before it can adopt this contract; it is not implicitly protected by this helper.

`fresh-onboarding-journey.sh HOST MINI STORE CREDENTIAL_VERIFIER NEW_RUNROOT` creates
a private deployment using `genesis.sh` and `genesis-params.example.json`. It checks
first trust at accepted-count zero, guarded resource creation, repeated onboarding
without downgrade, historical checking, missing-anchor refusal, and restart. It
uses an existing continuity-capable Host; it performs no native build.
