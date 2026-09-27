# Source-owned capability presentation and app-observe continuation

`Host/CapabilityInspection.lean` decodes the actual stored-capability codec and
presents every authorable head field as source-derived JSON. Naturals remain
decimal strings. Canonical bytes retain the full ancestry; JSON is structural
presentation, not current authority. The caller must supply the kind from its
authenticated query. Capability bytes alone do not infer that kind.

`Host/Json.lean` adds explicit `view-object-capability`,
`view-account-capability`, and `view-program-capability` inspectors. The existing
`view-capability` response is unchanged. The focused executable check exercises
nondefault issuer/policy epochs, inherited channels and root, an integer larger
than JavaScript's exact integer range, and malformed/trailing input refusals.
The helper and Host.Json compiled in an independent copy of the certified 2649
cache on Persvati; the corrected check ran with Lean 4.30 and exited zero.
An initial check-only harness used unavailable Except equality/isError helpers;
explicit constructor matches fixed that harness without changing production
source. The three final logs are retained here.

`scripts/spk-platform/delegate-app-observe.sh` continues an existing integrated
Store. It derives Bob and Hermes A/B observe-only child grants from signed
current parent-capability and app reads, inheriting issuer, epochs, validity
bounds, root and channel restrictions instead of copying fixture constants.
It requires matching current boundaries between parent and target reads;
native prepare/admission checks again. Each accepted delegation is followed by
the recipient's signed app read, with receipts retained in a new private
attempt. Uncertain/failed attempts are preserved, not automatically repeated.
The source-qualified Host with the new inspector is required; 2649 alone lacks
it. Create an owner-private `PREPARED_ROOT/continuations` parent beforehand.

The script passed syntax and ShellCheck. It has **not** been run against the
integrated Store. No new native Host was linked for this evidence, and no app
grant or user-access claim follows from these source checks. The fixture's
reserved app-observe coordinates are Bob 184, Hermes A 274 and Hermes B 374.
