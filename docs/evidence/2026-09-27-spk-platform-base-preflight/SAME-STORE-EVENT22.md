# Event22 continuation in the integrated GitWeb Store

This is a source-grounded continuation recipe, **not an accepted ticket**. It
must start from a qualified integrated base and later lifecycle INSTALL in the
same Store. `scripts/application-share-issue/native-grain-acceptance.sh` is a
separate fresh synthetic fixture: it bootstraps another Store and hardcodes
tasks 7901/7902, a human session, packageVersion 0 and budget 38. It cannot
issue the agent ticket for this Store by substituting paths.

For Hermes A, `scripts/spk-platform/allocation-v1.json` reserves app 8401,
API session 8420/descriptor 8421, ticket 8520, controller task 7920 (subject
10, key ID 10010), tool task 7930 (subject 11, key ID 11011), parent owner
capability 201 and delegated parent-tool witness 203, tool owner 211, session
owner 241, ticket owner/control/observe 271/272/273. Hermes B has its own
coordinates. The signed GitWeb identity selects package root
87005803221096792113550003106028498326059648433438765766069915491574610318393,
API interface ID/version 2/1 with interface root
16445804020461737684443349038626961901395635045771526464786662868335098993478,
and schema root
27586312506136906444761485190217684760117883013262689471085630892456074924140.
These are candidates until the same Store's signed installed app/package view
confirms version 1 and the exact roots.

The continuation must obtain fresh signed views under the qualified current
Host/config: app and package with issuer subject 8's owner capabilities;
session/descriptor and parent with subject 10's capabilities; tool and
delegated parent witness with subject 11's capabilities; payer account with
its actual spend capability. It must check current roots, generation, status,
remaining/reserved balances, authority and image boundary. If the parent or
tool needs a reserve, author the exact source grain intent from those views,
retain its original receipt and re-read before planning. The required tool
reserve must come from the source fee/plan and actual current balance, not a
copied `38`/`3` assertion. Choose a fresh issue nonce and verify ticket 8520
is still absent.

The Host-authored `application-share-issue-grain-request` must name ticket
8520, the signed installed scope, API session 8420/descriptor 8421, subject
10 with agent origin `{task:7920,generation:<signed current generation>}`,
session capability 241, ticket observe capability 273, an operator-approved
role ceiling tied to the current schema, and exact tool/parent selectors.
Payer/funding/source capabilities must be operator-approved and then compared
byte-for-byte through request inspection. The operator socket alone may plan
and assemble the issue. Its current-image plan fixes every signing slot; map
each `keyId` to the separately held issuer/controller/tool/payer key only after
checking role, index, canonical header and public key. The private Mini custody
helper then prepares exact ingress, submits op54 once, retains the four-field
receipt, and performs a lookup after service restart without resubmission.
Read ticket 8520 under subject 10's valid observe grant, compare signed
resource/fee and the original receipt, and verify no second Store charge.

The ticket's `participant.appObserveCapability` must be usable by subject 10
for app 8401 at dispatch. Base app owner capability 141 belongs to subject 8.
The updated allocation reserves observe-only children 184 for Bob, 274 for
Hermes A, and 374 for Hermes B. The new
`scripts/spk-platform/delegate-app-observe.sh` stages signed same-Store
delegations and recipient readback from the current app owner. It requires a
qualified source-owned capability inspector so that parent bounds, epochs,
issuer, and channels are inherited from a signed current view. These planned
IDs and the script are **not evidence of installed grants**. The continuation
must complete and produce exact native receipts before any final ticket names
them. Do not put 141 in an agent ticket merely because the issuer holds it.
