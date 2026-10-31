# Exorcism: continuation (start here)

Lane `lane/exorcism`, worktree `/Users/ember/dev/minidregg-lanes/exorcism`. The findings table and
every landed batch with its numbers are in `docs/EXORCISM.md`. Integrator: aba0beaa578594e92.
Hot-path (a6c4a1532687a4fdb) owns submit, story growth and FORMAT; this lane owns the Host's own
per-request time on the read and query path, aiming at ember's bar of about 1 ms warm.

## In flight

- `b168332a1` (Lean, not yet built into a Host): key status (op 144), the well ledger, the seat view
  and the key-commitment plan read `Opened.authority` instead of `loadDeployment` (an encode and
  decode of the 7 KB authority cell, 3.2 ms of op 144's 4-5 ms). Its `issuerCheck` half moved to
  hot-path (they adopted `existsSupport` verbatim; this lane removed its copy in `93b5fef03`).
- `lane-check` of `Kernel/NativeHost.lean` and `Kernel/NativeHostKeyCommitmentAdoption.lean` was
  running in pool tree `/home/hbox/pool/t6` (`/ci/exo/lc3.sh`, PID file `/ci/exo/lc3.pid`, results
  `/ci/exo/lc3.log`); it was rebuilding stale imports. t6 still carries an uncommitted diff to
  `Compiler/CredentialAuthorityPolicyRegistry.lean` from before `93b5fef03`: check that file out at
  the lane head before reusing the tree. t6 is leased to `exorcism`; `lane-tree release exorcism`.

## Next

1. Finish the importer checks; send `cad5a66fb` to the integrator for a Host build; measure op 144
   and op 5 on `/ci/exo/w` with `MINIDREGG_HOST_TRACE=1 bash /ci/exo/w/restart.sh` (traces land in
   `/ci/exo/w/log/store.log`) and `/ci/exo/m5b.py MINI N "key-status" "doc show xafter228813"`.
2. The rest of a signed read (op 5), agreed with hot-path as this lane's (submit runs them too), from the perf profile (`/ci/exo/hd.data`, symbolized with
   `perf report --symfs /ci/exo/symfs --comm 8`; `/ci/exo/agg.py` aggregates `perf script` chains):
   - `ContentResource.project` encodes the whole document cell (`StoreCodec.encode`, through
     `contentBytes`) for both `before` and `after`, which are the same store on a read: about 8%.
   - `FiniteDependentMapCachedOrdering.fromEntriesCached` re-keys every entry (`addressKey`
     encodes each address): about 4%.
   - `loadPolicy` re-encodes the policy record (`PolicyRecordCodec.encode`): about 3%.
   - `storedCapabilityDigest` hashes each candidate capability of the issuer's epoch: about 3%.
   - `Theory/CredentialAuthorityState` `parentKeys`/`revokedKeyAt` take `logical.support`
     (quadratic dedup) on authority loads.
   Hot-path keeps the ServedAuthority projection, the `Patch.run` Store.set chain (tell it if a
   read hits `Patch.run`), DRC `writes`/`readGuards` and FORMAT.
3. The challenge (op 4, 1-2 ms): not profiled yet.
4. Rows 6 and 8 of `docs/EXORCISM.md` (small).

## How to measure (hbox)

- A Host op straight to a socket: `/ci/exo/hop.py SOCKET OP N` (`/ci/exo/host.sha` holds the
  candidate Host digest).
- Profile the Host: `perf record -F 499 --call-graph dwarf,16384 -o OUT -- bash -c "bash
  /ci/exo/w/restart.sh; sleep 900"` with a PID file, drive requests, `kill -INT` that PID. The Host
  runs from a deleted memfd; `/ci/exo/symfs/memfd:mini-pinned-image (deleted)` is a copy of the
  candidate's `minidregg-host` so `--symfs /ci/exo/symfs` resolves it.
- `minidregg-host CONFIG store-bench` times loads (`loadDeployment x10`, `validateServedFrom`, ...).

## Rules carried

PID files for every process; stop only by PID file; no `pkill -f`; named-file commits with
`git commit -F`; filtered tests; swarm-build; one Lean closure at a time (the integrator's).
