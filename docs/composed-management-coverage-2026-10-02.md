# Composed management receiving coverage

Source audit by Codex /root/composed_management, October 2, 2026. These are
construction checkpoints, **not native qualification**. Base: law-composition
b1da9cc2. No extra Lean compiler was started; integrator owns compilation on the
shared two-seat schedule. Source commits: 79ca0c8e, 03b7d0b6, 7f1d3d37, 6897b32b.

## Why a local neutral check is insufficient

A child's local record can remain neutral while an ancestor exports a restriction
or its instance kind exports a restriction. Checking `PolicyRecord.neutral` on
the child does not establish that the effective law is neutral. Every existing
management target below is resolved from the source-owned authenticated snapshot;
none was exempted merely because it is an operator or system operation.

`WorldKindLawDependencies.targetSelectorSlots` supplies the actual stored kind
and ordinary-operation birth coordinate ahead of extensible payload slots.
`loadTarget` must separately succeed. Composed admission uses the existing source
capability checker and shared law compiler. Physical guards retain the current
and pinned source chains, kind definition and target identity. Missing dependency
material refuses; `.getD []` is only the list projection after a mandatory success
condition, never an admissible fallback.

## Receiving matrix

| Legacy consumer | Source target / effect | Current ownership and implementation |
|---|---|---|
| CapabilityDelegationController | Exact delegated resource | Migrated 79ca + selector 03b; actual CapabilityDelegationReceiver CAS guards. Parent naming evidence retained. |
| CapabilityRevocationController | Exact revoked resource | Migrated 79ca + selector 03b; actual CapabilityRevocationReceiver CAS guards. Current control capability retained. |
| RealmWellReceiver | Mint: well; burn: debited account | Migrated 7f1. Same Book batch and existing accounting proofs; target's ambient/kind restrictions now required. |
| JobMoneyReceiver | Source-selected money authorization target AND changed job | Migrated 7f1. Account/target composed portal plus shared resolved effect-law check on actual object mutation view; both dependency sets in CAS. Built-in job law identity and existing local job checks retained. |
| CertifyReceiver | Deployment factory | Migrated 7f1. Exact factory source restrictions and current/pinned physical guards; no-grant refusal pole retained. |
| ClockTickReceiver | Actual clock physical cell | Migrated 7f1. Clock is an existing source target, not exempted as a system singleton. |
| PurseRefillReceiver | Debited account AND changed task purse | Migrated 7f1. Account composed portal plus shared resolved effect-law check and guards for purse; original local purse check retained. |
| PayAssignmentReceiver | Account receiving deposit-address assignment | Migrated 7f1, with payment owner's ownership agreement. |
| PayBookReceiver | Deployment factory governing book/tariff management | Migrated 7f1, with payment owner's ownership agreement. |
| ParticipantKeyEnrollment | Deployment factory | Migrated 7f1 plus ParticipantKeyEnrollmentReceiver guard custody; key/possession checks unchanged. |
| ParticipantFactoryProvisioning | Deployment factory | Migrated 7f1 plus ParticipantFactoryProvisioningReceiver guard custody. |
| ApplicationShareIssueDelegation | Current app delegation leg | Migrated 6897. Both ordinary and grain admission retain full read-only guard list; both physical receiving paths install that list. |
| ApplicationAgentLifetimeGrantDelegation | Current app delegation leg | Migrated 6897. Lifetime admission and IntentTemplate retain complete guards and exact current-root proofs. |
| ApplicationLifecycleCompletionPolicy | DRC's exact incidence target, with checked completion slots | Migrated 7f1 by reusing DRC.policyConfigFromStep. Existing completion admission requires DRC.PhysicalShape and its complete dependency custody. |
| ApplicationLifecycleCompletionV2Policy | Same, V2 checked completion context | Migrated 7f1, same shared DRC path. |
| PayEnrolReceiver | Enrollment source authorization / new-member effects | Payment owner owns concurrent v2 receiver changes; API and guard pattern sent. Not migrated by this lane. |
| PayObservationReceiver | Verified observer / chain-tip source authorization | Payment owner and pay_operator_transport own concurrent receiver changes; not migrated here. |
| ResourceBirthPolicyController | Existing factory/account branches; newborn laws distinct | rooms_native_merge/birth_exports owns current birth export construction. Existing branch legacy configs still require explicit closure migration, not only newborn export gate. |
| GrainResourceBirthAdmission | Same factory/budgeted grain birth branches | Birth owner; do not treat added newborn gate as evidence that every existing branch is composed. |
| FnSelectiveReleaseSourceAuthority | Source read/release authority | docuverse_interface owns migration and downstream guard receiving paths. |
| FnConsumerFrontierGateway | Frontier source authority | docuverse_interface owns migration and exact current/pinned guard custody. |
| FnSelectiveReleaseAdmission | DRC-backed effect with custom owner portal | docuverse_interface owns composed owner-portal adapter; existing DRC physical guards must remain. |
| FleetTurn | Payer account transfer and account-owned derived stream metadata | docuverse_interface owns classification/migration; must establish derived metadata invariant before exempting a separate effect target. |

## Narrow receiving checks still required

1. Neutral child beneath exported deny(delegate): real delegation refuses and
   authority root/nullifier/balance remain unchanged; repeat for revoke.
2. Same denial selected by the child's actual physical kind. This catches a
   missing `target/storageKind` even when unselected denial passes.
3. An explicit/pinned historical dependency or instance kind export refuses;
   unavailable source/history/kind material also refuses without effects.
4. A current ancestor changes between preparation and commit: CAS cannot accept
   the old authorization. Existing exact historical replay remains receipt-only.
5. Neutral app local law plus inherited delegate denial refuses both share ticket
   and lifetime-grant issuance; no ticket/grant cell or debit is installed.
6. The same inherited restriction applies to checked STOP completion while a
   selected unrelated verb remains usable. Test V1 and V2 completion adapters.
7. An account's transfer law allows a job action/refill, while the actual job or
   purse ancestor refuses object mutation: native receiver refuses the entire
   Book/object turn. This falsifies account-only migration.
8. Existing no-grant, stale-root, source capability holder and parent-substitution
   refusal cases remain; composition does not replace credential authorization.

Rooms' native journey owner was asked to add cases 1–3; integrator receives the
full compilation queue. No PASS claim is recorded before actual compiler/native
results arrive. Budget exhaustion remains a refusal rather than truncating laws.
