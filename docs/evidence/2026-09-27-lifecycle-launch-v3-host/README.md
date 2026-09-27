# Launch-bound v3 Host source gate (2026-09-27)

The source cut authors INSTALL, first-create START, and verifier-selected
continue BEGIN plans through private op66/67; authors event24 claim through
private op68/69; submits fresh event23/24/25 through the typed receivers; and
performs strict receipt-only historical lookups. Op26 hands out a committed
launch frame only after the receiver reports the actual `.installed` CAS winner
and `withFreshTip` rereads the exact physical tip. An already-present image,
recovered uncertain response, or historical lookup returns a receipt outcome,
never a launch frame.

The check used an independent writable hbox overlay at
`/tank/dregg-build/minidregg-fn-frontier-narrow-20260927`, based on the
immutable exact-55d3868 292-module prefix. The overlay imported committed
`NativeHostContext` source `3fc07451`/OLean `b91b8102` and canonical-byte
`NativeHostReplay` source `a29e19f8`/OLean `63169cba`; the final Main gate also
used `DurableReceiverIO` source `6f13945c`/OLean `2fbf2652` and
`ApplicationLifecycleClaimV3Receiver` source `6bbcfc92`/OLean `e4bdd75a`.
All six Host modules were compiled serially with `LEAN_NUM_THREADS=2 lake env
lean Host/NAME.lean -o .lake/build/lib/lean/Host/NAME.olean`, each exit 0.
Five final logs have no diagnostics; Json has pre-existing axiom/linter output
and no errors. `host-v3-Main-final.log` is the final Main source gate; the
earlier `host-v3-Main.log` is a superseded diagnostic.

Focused `cargo nextest` broker test passed 1/1 and `cargo fmt --check` passed.
The evidence is source-level only: no linked Host binary, live CAS, process
launch, protected-volume witness, or native acceptance is claimed. The
read-only committed-v3 frame inspector and op70/71 completion authoring are
separate follow-up source modules, outside this Main gate.
