# INSTALL Host upgrade and STOP journal hook, component gate

`prepare-install-config.sh` now accepts an explicit source-qualified v3 Host
pin while retaining the exact earlier base Host pin. The binary may be reused
when the base was already created with the qualified successor; evidence records
that case explicitly. Before emitting a v2
INSTALL config it reopens the same protected Settings and Store with both
Hosts, compares their fixed runtime/profile description, looks up the original
base app call, compares the exact four-field receipt to the base record, and
checks the Store image did not change. It retains both executable identities
and the replay evidence under `source-stage/install-host-upgrade`. The v2 config
pins the retained launch qualifier and the deployment/host IDs read from the
root-owned volume service identity. The IDs are expectations for a later
physical volume witness, not a root attestation made by this script.

The new hostd STOP hook accepts an exact prior running incarnation and a
source-bound volume recheck callback. Under the journal lock it checks both,
confirms systemd's invocation and cgroup, fsyncs a Fenced tombstone before the
manager stop, then requires the exact post-stop audit before recording Stopped.
If the manager reply is lost, reopening Fenced can audit the same stopped unit
without another Mini claim. The hook is not yet called by physical STOP;
`FreshStopClaim` and the retained event25 witness join are separate work.

`sh -n` and ShellCheck passed for the script. A private hbox Linux snapshot
with only the owned hostd file updated passed one focused injected-drift and
Fenced-recovery test, plus strict all-target Clippy. These checks did not open
a live Store, run a systemd STOP, or accept a v3 INSTALL/START fixture. Exact
source and log hashes are in `SHA256SUMS`.
