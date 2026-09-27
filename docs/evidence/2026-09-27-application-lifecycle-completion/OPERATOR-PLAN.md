# Current-image completion signing plan

This source-only checkpoint fills the gap between a signed physical report and
event-18 native admission. No report, plan, or assembled ingress by itself
authorizes process launch or marks completion.

`Host/ApplicationLifecycleCompletionOperator.lean` SHA-256
`1f9b7b48414f41a84bcbee57e1c40e361ccc8993f3f824930ce3646b29c92395`
defines a strict request, plan, and two-stage API. The private Host settings
must pin app and package IDs, management subject and key ID, and app/package
mutation and observation capabilities. The request contains only exact
BEGIN-v2, claim-v2 ingress, and signed custodian report bytes. Preparation
uses the verifier-admitted current tip to check the custodian signature,
same-walk claim, exact historical projection, current app/package state,
installed policy and physical shape; it derives the command and all target,
observation and authority headers through `NativeHost.prepareLoaded`. The
separate package header is derived from
`ApplicationLifecycleCompletionAdmission.packageRequest` and the same current
authority snapshot. Every header's key ID must equal the operator pin.

`Host/Json.lean` SHA-256
`7e215445c5677d61b75bcdf4e5c5d6e4dd24df5d206e3a9717f5861a6eb242b5`
adds the strict `application-lifecycle-completion-operator-request` author kind
and `application-lifecycle-completion-operator-plan` inspector. The inspector
echoes canonical plan/source/command bytes, current image boundary and height,
and ordered exact signing headers. The fixed signer signs those headers in
order; assembly inserts detached signatures and emits event-18 ingress. Op38
still re-admits current law, signatures, original claim and the exact physical
report, then performs one CAS; op39 remains receipt-only.

The two files compiled serially in the independent Persvati completion overlay
at `/tmp/minidregg-completion-{src,olean}`. OLean SHA-256 values are
`8857f871d089c82e56d25305b6242d0d8d30c2d54081126bcf3e61a0a9afb671`
and `cde49111cfdaaa539b3cdb054540553653df6106737e6338a40d7d5156544139`.
The final Host.Json direct Lean log is
`/tmp/minidregg-completion-Json.log` on Persvati, SHA-256
`329429c329d18f72c4fe75692e45a2592d0fead9e71040d480361d35887d5624`.
Host.Main op44/45 settings/routing and a source-matched native build are
separate pending gates; no live Store or host service was used here.
