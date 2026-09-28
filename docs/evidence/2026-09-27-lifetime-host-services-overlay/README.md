# Post-grant A/B Host selector overlay

`scripts/spk-platform/prepare-lifetime-host-services.sh` consumes a private
qualified base Host config and the two retained `prepare-lifetime-route.sh`
output directories. Each directory must carry the exact source-inspected
accepted event27 grant, controller route, resident custody, canonical ingress,
and SHA manifest. The script joins event22/event27 indices and full receipts,
lineage, grant digest/root, route identity, and every legacy event26 selector
before writing a two-entry `agentLifetimeDispatchServices` config. It refuses
legacy scalar agent dispatch pins in the base config. It then reselects both
grants read-only through the pinned Host using the final config and requires
the entire current source projection to equal each retained handoff. It never
submits an event or starts an app.

`schema-only-linux.log` is a synthetic, source-shaped hbox test with a fake
read-only Host. It produced separate A and B selector tuples, then refused an
altered grant receipt, a legacy scalar collision, a duplicated A route, and a
changed current source projection. `shell-gates.log` records shell syntax and
ShellCheck. This test does not establish native event26 admission or accepted
r3 event22/event27 grants.

`r3-budget-readonly.log` pins the current retained r3 tariff and signed
tool/parent views. Source `GrainResourceBirthController.Tariff.charge` is
`base + perBirth × births`; event22 and event27 each create one birth. With
the configured `2 + 1 × 1`, seven separate issues charge 21 from tool7902's
remaining 25, leaving 4 if no other writer intervenes. Each issue needs its
own fresh reserve of at least 3 because settlement clears the reserve.
Parent7901 is an exact-state witness and has no grain charge. This does not
quote the separate factory fee: event22 has fixed base/birth/grant component
7 and event27 has component 8, each plus source-derived final payload bytes.
Current op56/68 plans must supply the exact fee and confirm payer funding.

The r3 candidate ticket inputs are separately retained under hbox
`/var/lib/minidregg/spk/fixtures/gitweb-v2-20260927-operator-inputs-r3`
(directory 0700, files 0600). They pin accepted app/session birth receipts
17/19/21/23/25/27 and signed package schema role 1, whose permissions are
`[true,true]` for read and write. The four known signing keys in its private
`ticket-signers.json` are public-key matched to their enrollment: subject 8
`workroom/tool.key`, Bob subject 9 `workroom/member.key`, and agent controllers
10/20. No seed bytes were copied or printed. Ticket policies are candidate
inputs; current op56 planning and op54 admission must approve them after
INSTALL/current package selection. No r3 ticket or grant exists yet.
