# Exorcism: continuation (start here)

Lane `lane/exorcism`, worktree `/Users/ember/dev/minidregg-lanes/exorcism`. The findings table and
every landed batch with its numbers are in `docs/EXORCISM.md`. Integrator: aba0beaa578594e92.
Hot-path (a6c4a1532687a4fdb) owns submit, story growth, FORMAT, the ServedAuthority projection,
`Patch.run` and `issuerCheck` (it carries this lane's `existsSupport`). This lane owns the per-request
cost of a signed read end to end, aiming at ember's bar of about 1 ms warm.

## Where a one-shot `doc show` goes (hbox /ci/exo/w, candidate a4cb65af, light strace)

About 40 ms of wall time:
- Host op 5 (signed read) 9-13 ms, op 4 (challenge) 2-4 ms, op 144 (key status, the
  workspace's commitment recheck) 5-10 ms;
- codec resident frames 3 ms (author 0.2, challenge JSON 0.6, signatures 0.1, signed observation
  0.2, view-resource 1.1, view-document 1.0);
- consent resident 2.8 ms (two frames; each Store read went through a temp dir);
- client: process start and workspace load about 4 ms, then about 60 openat as an attempt-file bus
  (it writes intent, challenge, signatures and views, then reads them back; `config.json` is read
  about eight times).

## Riding batch 6 (merged to staging), not yet measured

- `b168332a1`: op 144 and three other readers use `Opened.authority` (3.2 ms of op 144).
- `bcccac6cc`: the ssh wrapper execs mini, which holds the call slots (whoami 9.8 to 4.0 ms).
- `16f2d046f` + `019f2e56f`: the commitment-seen cache is reverted (review); check_commitment
  refuses an explicit `currentRevoked: true`.

## Sent, not yet merged

- `8b49bf1e2` + `fe77ab521`: Store calls carry their files in the coprocess frame (frame v2,
  `NativeCoprocess.outputMemory`, Store helper `mem:NAME`); the MAC key is read once per process.
  The Host and its Store helper must come from the same build.

## Next, in order

1. Measure ops 144, 5 and 4 and the consent resident on the batch 6 candidate (then batch 7 for
   the memory frames). Overlay on /ci/exo/w: `bash /ci/exo/w/restart.sh` restarts Host and Store;
   `MINI_TRACE=/abs/file` gives per-op client times.
2. Profile op 5 on the new Host (perf `--call-graph dwarf` works on the on-disk residents; the
   operator Host runs from a memfd, so copy its binary under a symfs as before). The read-path
   costs agreed as this lane's: `ContentResource.project`'s double encode, `fromEntriesCached`
   re-keying, the `loadPolicy` re-encode, `storedCapabilityDigest`. Hot-path's 545f80874 (demand
   projection) postdates the old profile, so re-profile before changing them.
3. The client's attempt-file bus: keep the values in memory and write each retained file once.
4. The consent provider reads the Store twice per connection (`recheckHeld` from `height`, then
   `extendFrom` from `height + 1`); one read serves both.
5. Codec frames: the view is decoded twice (view-resource, then view-document).

## Rules carried

PID files and timeouts for every remote job; stop only by PID file; named-file commits with
`git commit -F`; filtered tests; swarm-build; no Host build on hbox while it is under 50 GB free
(the integrator builds candidates); `/home/hbox/lanes/exorcism` is the Rust-only clone.
