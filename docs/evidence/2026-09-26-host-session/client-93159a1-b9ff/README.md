# Pinned client acceptance and service restart

The native resource-client acceptance driver passed against one immutable
client and one source-matched, linked Host/Main binary on 2026-09-26. This is
a later checkpoint than the initial replay-poison host documented in the
parent directory.

- Client source: commit `93159a1`; `src/main.rs` SHA-256
  `9393531200cf0927ae76957b30fa2d9f1fb4d01d5f15a1315cdf0373dcdc82bf`,
  `src/transport.rs` SHA-256
  `ca7cc5971f5bc060a0547c7d517fd7f770cc39d6be7ccffd5eea244a0f1f4a99`.
- Immutable client binary: SHA-256
  `9384047b5949744ff6fa0317a3daa0cd8d3167c207a804a6907152a4025a65e3`.
- Linked native host: SHA-256
  `b9ff9832b13ad67124e753ab52122732bfe9b795653e2ba64c1e0f35b051ee8a`.
  Its build manifest records 163/163 source module hashes and 3096 native
  objects, with the Host.Main dynamic A claim source but before later inbox
  and catalog changes.

The [acceptance result](acceptance.json) reports `status: pass`: birth,
content, and joint submissions confirmed, with the deliberately lost content
response recovered using the retained exact signed call. The client had
synced `call.bin` and its directory ancestry before submission. The private
run was `/tmp/minidregg-client-93159a1-b9ff-acceptance`; no raw call, key,
store, or operator config is copied here.

The same client checkpoint also passed a private same-path service restart
probe at `/tmp/mini-service-restart.PbYos0`: profile responses before and
after restart were byte-identical; a simultaneous second service was refused
by the owner lock; a changed config was refused after stopping the first
service; and the existing owned stale socket was recovered. The restart
probe used the earlier initial host image, not the `b9ff` image above. These
are separate, scoped results.
