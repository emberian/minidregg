# Native client signing consent

A participant's signing key must not sign a preimage chosen by the operator. The
operator can propose a challenge or plan; custody derives the complete expected
bytes from its retained request, its own configuration and an independently
admitted source prefix before releasing a signature. Local decoding alone does
not establish that relationship. Matching a nullifier or an unsigned draft is
also insufficient: legitimate birth preparation can finalize the draft, and a
signing marker need not independently encode every effect.

`Kernel.NativeClientConsent` implements ordinary observation and preparation
consent with private checked constructors. `Host.ClientConsentCore` keeps the
independently admitted prefix warm, checks exact extensions before each signing
phase, and terminates on a rollback, prefix rewrite or invalid extension. It
never restarts a failed verifier to discard that frontier. The executable and
configuration are selected by local custody, separately from the remote Host
image pin. Private workspace and attempt manifests retain those local paths.

Rust `client_consent` gates the initial intent signature, every observation
signature and every ordinary transaction signature. Authoring, inspection,
signature encoding and ordinary detached assembly use an independently selected
local native image. Batch observations and enrollment's separate codec wrapper obey
the same rule. Exact locally retained codec frames are compared with current
local derivation before reuse.

`Kernel.NativeSpecializedConsent` reconstructs the complete canonical plan using
the production loaded planner, including the production encoder. The central
Rust transport boundary checks adapted plan responses before returning any bytes
to a signing consumer, including direct transport callers. The paid claim's HTTP
path performs the same check. A failed check never falls back to the proposed plan. A
retained unsigned plan also needs reconstruction before signing: the reserve
seal, lifetime reserve/grant seals, provisioning seal and enrollment sponsor seal
perform that check explicitly. Existing signed
ingress and uncertain submission outcomes remain retained for exact lookup or
resubmission; they are not replaced by a new signing decision.

The base specialized entry supports these native plan operations:

| Operations | Planner family |
| --- | --- |
| 86, 92 | Participant key enrollment and factory provisioning |
| 96 | Fleet turn |
| 103, 108, 113, 117, 183 | Pay command, observation, refill, current enrollment, claim |
| 123, 126, 160, 170 | Well, clock, job money, certification |
| 140 | Subject key rotation |

This reconstruction binds the actual configured domain and runtime profile, the
entire retained request, role and index incidence, and all ordered headers. A
legitimate plan may contain several signers. Each signing consumer must bind its
selected local key to its intended role using local native inspection and its
retained signer approval; forcing every role to one key is not a substitute.

Enrollment possession is source independent: the actual native possession-frame
function derives bytes from the complete retained enrollment command under the
selected service domain and profile. The new local key and requested subject
must match that command before signing. An operator-offered command is still an
offer after it is saved locally. The possession action accepts that exact
command, so the command and its service/profile selection must be retained and
reviewable at the custody boundary. A private pre-sign acceptance record retains
the exact offered command, selected local configuration and custody identity. Sponsor enrollment consent additionally
requires current independently admitted source reconstruction.

`Host.ClientConsentSession` adds the lifecycle adapters from
`Host.NativeLifecycleConsent`; it uses an explicit locally selected
`lifecycleManagement` identity for managed families. The independent
`Host.ClientConsentSpecializedSession` entry refuses those higher families. A
compiled base entry does not establish qualification of the larger entry or its
dependency closure.

This is a full-peer producer. It neither sends the protected Store to friends
nor proves a thin client's selective state view. The current world root
commits an entire encoded cell, including the authority cell; opening that leaf
can disclose fields the friend was not granted. Supplying sparse defaults can
change a planner's reads and does not repair this. A thin producer needs a
checked read-footprint planner with authenticated granular openings and a
compatible commitment schema, or a proof of the native preparation against an
independently authenticated frontier. An operator's checked Boolean, view JSON,
plan/nullifier match or claimed footprint cannot replace that proof.

Qualification must name the exact source/import/native cohort and receiving
consumer. Higher lifecycle families, namespace/frontier plans, grain share
issuance, key commitment adoption, authenticated application plans, new generic
invocation-family profiles, and any remaining retained signing consumers need
separate coherent adapters and operational checks. Compilation of a helper
alone does not close those signing paths.
