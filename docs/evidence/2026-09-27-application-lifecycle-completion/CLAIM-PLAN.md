# Descriptor-bound lifecycle claim operator plan

An operator-private request contains only `originalIndex` and `queryNonce`.
`ApplicationLifecycleClaimOperator.prepareRequestVerified` selects the
descriptor-bound BEGIN from `Verified.beginsV2`, checks its complete retained
record at the selected index against the verified tip, and requires the fixed
management identity, app, package, and mutation capability. It derives the
current pending app state, authority/app/package roots, image boundary, and
the claim source from that authenticated BEGIN and the current image. The
source-owned plan contains the DRC invocation headers plus separate current
app and package observation headers; every header must use the fixed operator
key ID. START additionally sees the exact installed manifest named by the
original signed descriptor. A missing or changed package content cell refuses.

`assemble` accepts the ordered detached signatures and emits canonical claim-v2
ingress bytes. It does not refresh the image or issue a physical launch permit.
Native op26 must verify the historical BEGIN and current signatures, law,
roots, and one-shot pending-to-claimed transition again before a claim receipt
can be handed to the physical host.

The JSON author route `application-lifecycle-claim-operator-request` accepts
exactly `originalIndex` and `queryNonce`. The inspect route
`application-lifecycle-claim-operator-plan` echoes canonical plan/source/BEGIN
bytes, exact current roots and image boundary, and the ordered signed headers.
Private stdio op52/53 routing and linked native acceptance are separate cuts.

In a private Persvati overlay over the coherent selected-prefix base,
`Host.ApplicationLifecycleClaimOperator` then `Host.Json` compiled directly
with `LEAN_NUM_THREADS=2`. Both exited successfully. `Host.Json` emitted only
pre-existing unused-simp warnings and axiom-accounting output. This is a
source typecheck; it is not a linked Host or an accepted physical claim.

| Artifact | SHA-256 |
| --- | --- |
| `Host/ApplicationLifecycleClaimOperator.lean` | `435297893e70868e8f8df64c6fe8bd8407b87e14b1ba4b4782c92c943e722342` |
| `Host/Json.lean` | `6c137c78e2ad88f77b02ffdd255e8d9aae01adeb03aa6ebca52bfcb211748b72` |
| private `Host/ApplicationLifecycleClaimOperator.olean` | `1de33a581a3895fe17eb35ad919519484dd562eebd071788052b676077a83f10` |
| private `Host/Json.olean` | `98bc5c5fa3bd73e81c86370d0a3a016d5161ecd3254a04ab13fa0ff09ab5c377` |
| private Operator compile log (empty, successful exit) | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| private Json compile log | `1903389907f5a5a2f1da59eb1b8f881e1520b9c9b5fb14ef89266bb34306e770` |

The private source and output paths are `/tmp/minidregg-completion-src/Host/`,
`/tmp/minidregg-completion-olean/Host/`, and
`/tmp/minidregg-claim-{Operator,Json}.log` on Persvati. Shared source files
were compared by SHA-256 to their compiled private copies.
