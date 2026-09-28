# Event27 operator issuer, schema gate

`scripts/spk-platform/issue-agent-lifetime-grant.sh` stages a candidate from an
exact retained event22 attempt. It first performs op55 receipt-only lookup,
compares the original four-field receipt and source-inspected ticket digest,
then asks Mini op74 for a current grant plan. Operator approval pins every
source-selected signing header and protected signer; Mini op75 assembles the
ingress. `finish` calls op72 at most once and uses op73 exact lookup for
recovery. The original event22 ingress/plan hashes and executable pins are
rechecked before sealing or finishing.

Validation: `sh -n` and ShellCheck passed. An isolated Linux schema fixture
exercised prepare, approve, seal, one submit and exact lookup, plus repeated
finish, changed source parent, and changed original event22 ingress refusals.
The fixture uses fake Host/Mini programs to check shell transport and retention;
it does **not** establish Mini admission or a live r3 grant. The r3 Store has
no accepted event22 ticket yet. Source op74/op75 and native op72/op73 remain
the authority for eventual live use.

The exact fixture was run on hbox in
`/home/hbox/mini-agent-grant-schema-fixture-r5`; the test driver and fake
programs are local fixture artifacts there, not part of the deployment path.
The retained log is `schema-fixture.log`. `negative-schema.log` is the r4
negative run against the same issuer implementation.
