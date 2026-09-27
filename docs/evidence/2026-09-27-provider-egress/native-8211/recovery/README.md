# Same-deployment hard-EOF recovery continuation

This continues the private task-8211 Store from the parent evidence, without a
new prompt or provider call. The first run's final signed-query projection
showed parent status 3, generation 1, remaining 96, reserved 3 after the
runner stopped the controller early. Its durable parent hold remained.

The first recovery connector raced the old, unbound control socket and got
`Connection refused`; it made no Mini call. A second connector sent `recover`
to the restarted controller. The controller confirmed native `interrupt`
operation 105 at acceptedCount 29. A subsequent read-only Mini query projected
parent status 5, generation 2, remaining 96, reserved 3, with root
`59360518788822303396743883036612208485749012866897084328219535012011594019833`.
The journal retained the parent hold and an explicit external-effects
uncertainty. [The exact operation and receipt](interrupt-and-settlement.json),
[post-interrupt query projection](post-interrupt-view.json), and
[recovery log](recover.log) preserve that boundary.

The private deterministic fixture's provider log still contained exactly the
three earlier read, publish and complete stages; no provider server was started
during recovery. After inspecting the stopped worker, the retained call and
the fixture log, an operator command `reconcile parent audited` confirmed native
fixed-charge settlement operation 109, charge 1, acceptedCount 30. A separate
`reconcile effects` command then returned `ok`. The journal is detached with
no child, pending call, held charge, provider attempt, or unresolved external
note. A final read-only Mini query projected parent status 0, generation 2,
remaining 98, reserved 0, root
`42856613354529666900040672388482651837645299109640673301270122874643233376381`.
See [post-audit journal](post-audit-journal.json),
[post-settlement query projection](post-settlement-view.json), and
[admin markers](settle.log). The projections were produced by Mini's signed
query path; this directory retains hashes of the exact signed observation and
view bytes in [readback-and-cleanup.txt](readback-and-cleanup.txt), not the
complete attestation files.

The same runtime/config and Host/Mini images were used throughout. Exact
private script/config and native outcome hashes are in
[private-source-and-outcome-sha256.txt](private-source-and-outcome-sha256.txt).
The first-run hard physical stop was confirmed before this continuation; the
continuation proves the signed fence and audited settlement, not an automatic
settlement on EOF. The controller unit was inactive with MainPID 0 and no
bridge process remained. The old private provider Unix socket may remain as a
mode-0600 stale inode after systemd stop; the controller's owned stale-socket
reclaim is separately covered by the Rust component tests.
