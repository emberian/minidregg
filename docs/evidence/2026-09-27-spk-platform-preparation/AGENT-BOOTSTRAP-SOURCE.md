# Integrated agent bootstrap source cut

This cut prepares, but has **not executed**, one fresh Store continuation
after the signed GitWeb v2 `qualify-launch` gate. No native admission, ticket,
installed manifest, resident process or app request is claimed here.

The reservation correction replaces agent A account resources 10/11/12,
which conflict with Mini genesis factory/resource-book/catalogue IDs, with
8010–8013; B uses 8020–8023. The eight genesis factory-observe caps are
610–617. Source `NativeHostGenesis.Config.Valid` requires the accounts and
deployment IDs to be pairwise distinct. `agent-genesis-overlay.sh` additionally
checks the combined known resource and capability namespace before emitting
private source. Two negative scratch allocations (account 10 and capability
54) were refused before output creation.

`run-base.sh` now invokes the genesis overlay only **after** its positive
one-SPK v2 qualifier. The overlay generates eight independent keys and
enrollments before bootstrap, adds eight grains to the first signed birth,
requires the confirmed birth receipt and eight owner-signed resource views,
compares each parent's installed policy bytes to the source-authored
generation-1 law for its three named tool/dispatch/provider workers, and
submits six distinct owner-signed parent-witness child delegations. It
requires each holder's signed resource readback. The initial worker policy
and the child grants are separate authority checks. A later controller
renewal must include the dispatch worker before a hard attach advances the
generation; static generation-1 witness authority cannot be reused.

`agent-session-overlay.sh` extends the existing current-image metered source
chain with Bob Web 8406/8407, Alice API 8410/8411, and agent API 8420/8421
and 8422/8423. Subject 8 signs each factory birth using a **fresh** tool
observation and reserve; the resulting owner subject 9, 8, 10 or 20 signs
its own session and empty-descriptor readbacks. Each exact birth receipt is
retained. Session birth does not install an agent origin or app ticket;
event-22 enrollment/issuance later binds the current parent generation.
Event-27 separately births reserved grant resources 8530/8531 only after an
admitted event-22 issue receipt. This source does not pre-create them.

The app and empty package/snapshot births remain separate from INSTALL.
`run-base.sh` retains a non-authoritative handoff with the one-SPK qualified
v2 `launchRoot`, canonical descriptor SHA, embedded v1 signed package root,
app birth receipt and the empty born content roots. BEGIN-v3 and completion
must later install the exact v2 root; the v1 root is not substituted for it.

## Bounded checks

- `sh -n` and ShellCheck pass on all five `scripts/spk-platform/*.sh`
  preparation files; `git diff --check` passes on this scoped cut.
- Both overlays emitted a syntactically valid source copy in private scratch.
  The generated provision source SHA-256 was
  `8b7a1e760db115f33643313b4140cab9ab70c6eb7ea4ce455c0f4c13cff0f1d8`;
  the generated app/session source SHA-256 was
  `80dfaf29545fb86ea420517179b7eb24f3bdcb42da1eb0a82043e67750861c68`.
- The current generated preboot fragment used the actual local Mini `keygen`
  to produce eight separate private scratch seeds. The resulting JSON had
  ten distinct enrollment public keys including two minimal baseline rows,
  exact planned accounts 8010–8013/8020–8023 and factory-observe caps
  610–617. This was a keygen/JSON shape check, not Mini bootstrap.
- A pure `jq` evaluation of the added birth resources yielded exactly eight
  grains; the two parent policies had worker lists [11,12,13] and
  [21,22,23]. A pure session-source evaluation produced agent A API session
  8420/descriptor 8421 owned by participant 10 with capabilities
  241–244. These checks do not substitute for native policy or birth admission.
- A synthetic retained-evidence shape passed the `run-base.sh` receipt
  selector; changing one parent-delegation capability caused refusal. This
  checks the handoff parser only, not a real receipt.

No fresh Store has been created. The source-qualified v2 Host link, actual
`qualify-launch` success, all native births/delegations, v3 INSTALL/START,
event-22 tickets, event-27 grants and physical A/B routes remain pending.
