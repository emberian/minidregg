# Resource workspace recovery acceptance, 2026-09-28

The current Linux controller journey is **partial**. A fresh private Store under
`/home/ember/build/minidregg-recovery-20260928/hermes-workspace-8701-a` reached
hard-stop reconciliation, then refused the first restarted attach because its
signed managed-worker policy was for generation 1 while the retained grain was
at generation 2. The controller did not bypass that check. A separate signed
owner source, `owner-policy-repair-source.json` (SHA-256
`883f750850614474d1eea1b31c3101291b04703f6afb174a6b87aa219958d5ba`),
installed generation 2 at `owner-policy-repair-attempt/outcome.json` (confirmed,
acceptedCount 16, SHA-256
`c1d0d53a4d5f8e10abcbd5a762609a2a0d3a716d492ed77446bfb6919b4843a8`).
This is **operator-assisted recovery**, not automatic restart.

After that repair, the controller recovered its fenced journal, installed the
next signed managed-worker policy at
`runtime-state/policy-attempt-0000000000000061/outcome.json` (confirmed,
acceptedCount 21, SHA-256
`774fb384c7880a4aada457c8b4558a17bd39ef88581e85859d34985872b84844`),
and admitted an attach at
`runtime-state/attempt-0000000000000063/outcome.json` (confirmed,
acceptedCount 22, SHA-256
`a7b2beafdfb17d7164084b3778df8b357010642d2752a1450dec5430fdf31859`).
It reached a soft, idle journal with no pending operation or unresolved external
effect. The attempted `hermes acceptance-publication` command then failed
before ACP launch with `Hermes config for MCP timeout: No such file or directory
(os error 2)`: the test fixture lacked the private `config.yaml` checked by
`provider_profile::require_worker_mcp_timeout`. No workspace MCP proposal or
submit was attempted on this current-image fixture. The `@8701` controller
unit was stopped and verified inactive; its private Mini server was stopped.

The paired source-qualified Linux artifacts were Host `e22d16b` SHA-256
`723940446d3e0256bd446b07ca8d67ea9d67295d8c7cc78e08bb2487ffbe3db2`,
Mini `0007925` SHA-256
`3e9cb1ca488995a0a591ea6db8f9b4b6b59d9629782daf6babb294620c74513d`,
and grain-runtime `f4d27d1` SHA-256
`a2c5493fe3f7ff5cbddcf93af28c158c25f3ca4b69c828c2577b87175f6de1c0`.
The separate historical Host fixture at
`/tmp/minidregg-hermes-workspace-20260928-a` demonstrated native workspace
named read, user-authored policy install, proposal submit, exact recover, and
scalar mutation, but does not qualify this current controller path. The focused
controller refusal/recovery regression and full fast Rust suite passed
(141/141). Neither fixture ran a full Nous Hermes inference/session turn.

The next acceptance attempt needs an explicit private Hermes profile in the
worker workspace, followed by actual MCP list/describe/read/propose/submit and
exact recovery on this qualified Host/client pair. The stale signed worker-law
generation after hard-stop remains a service continuity gap unless a supported
automated owner upgrade path is provided.
