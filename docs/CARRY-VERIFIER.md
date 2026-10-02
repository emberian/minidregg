# Carry verifier bootstrap

An old runtime can verify ordinary continuity without understanding a future
carry edge. Install the separate `minidregg-carry-verifier` under the existing
client authority before carrying. Its executable digest is an explicit local
trust choice; neither the service nor an edge manifest selects this executable.
The ordinary verifier, current identity, receipt anchor, and retained source
capsule stay unchanged.

The source target is `lake build minidregg-carry-verifier`. It imports the public
carry verifier, not the full Host receiving executable. The initial native
artifact is Linux-specific: it uses the retained local signature helper and
`/usr/bin/sha256sum`. Platform packages must provide a compatible pinned runtime
and crypto helper; copying this Linux binary is not a macOS package.

The executable accepts exactly:

```
minidregg-carry-verifier OLD_CONFIG carry-verifier-profile REQUEST_JSON RESULT_JSON
minidregg-carry-verifier OLD_CONFIG carry-edge-verify REQUEST_JSON RESULT_JSON
```

`OLD_CONFIG` must have the independently registered source configuration digest.
The client request supplies its previously pinned source capsule and identity.
Before either operation, the verifier rechecks the retained executable,
configuration, profile, and signature helper hashes, reads the original profile,
and runs the retained old executable to confirm its exact profile output. The
compiled target semantics are never substituted for the old profile.

The profile operation returns algorithm `minidregg-carry-verifier-v1`, the exact
source identity and capsule pins, and edge algorithm `minidregg-carry-edge-v1`.
It does not inspect an edge or run target code. The edge operation preserves the
public verifier checks: independently pinned operator, detached signature,
source and target system openings, original domain/genesis, one-step carry
height, and signed target executable/configuration/profile digests. It executes
the locally selected target only after signature authorization.

The matching client installer uses:

```
mini workspace --action continuity-carry-verifier --dir WORKSPACE \
  --verifier /absolute/minidregg-carry-verifier --sha256 LOWERCASE_SHA256
```

The artifact hash is checked before execution. The installer holds the existing
custody lock, checks the native source profile description, and records a
separate pin. A durable workspace marker precedes that pin, so interruption
requires explicit reinstall and cannot silently fall back to another verifier.
Missing, altered, or stale pins refuse carry. Ordinary receipt continuity keeps
using the old retained Host. After a carry changes identity, installing a new
portable pin is a distinct explicit local action.

The public edge attests an externally authorized handoff and its commitments.
It does not disclose the private Store or prove private semantic replay to the
client. The operator-side receiver separately audits the retained source and
validates target state. The client still verifies old-anchor-to-cut continuity
and the target endpoint extension before atomically adopting its new anchor.
