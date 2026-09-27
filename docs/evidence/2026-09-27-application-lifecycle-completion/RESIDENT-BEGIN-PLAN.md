# Resident INSTALL/START BEGIN-v2 operator plan

The operator request contains only `kind` (`install` or `start`), an operation ID,
and canonical signed-SPK descriptor bytes. `ApplicationLifecycleBeginOperator.prepareRequestVerified`
uses a verified current Mini image and a fixed deployment pin to derive the app's
current state, the next process generation, physical resident identities, current
authority/app/package roots, the exact DRC command, and its signing slots. It
derives a separate package-observation signing header from that same image.
The plan refuses a non-content package cell, a mismatched installed manifest
on START, a mismatched proposed descriptor, and signing headers with a key ID
different from the operator pin. INSTALL's manifest is prospective; it is not
asserted installed before checked completion.

`assemble` inserts the detached signatures into canonical BEGIN-v2 ingress
bytes. It does not refresh the image. The fresh native op22 admission must
recheck the signed command, package observation, current law, roots, and exact
prospective/installed descriptor before recording a pending BEGIN. The signed
SPK descriptor and operator pin are inputs to the deployment trust boundary;
physical host custody of the signed package is checked separately before launch.

The JSON author route `application-lifecycle-resident-begin-operator-request`
accepts exactly `kind`, `operationId`, and `descriptor`. The inspect route
`application-lifecycle-resident-begin-operator-plan` echoes canonical plan,
source, and descriptor bytes and exposes the ordered exact signing headers.
Private stdio op50/51 routing and a native linked acceptance are separate cuts.

Narrow source check, in a private Persvati overlay over the coherent selected-prefix
base, compiled `Host.ApplicationLifecycleBeginOperator` then `Host.Json` with
`LEAN_NUM_THREADS=2`; both Lean invocations exited successfully. `Host.Json`
emitted only existing unused-simp warnings and axiom-accounting output. This is
a source typecheck, not a claim of a linked Host, native accepted operation, or
physical launch.

| Artifact | SHA-256 |
| --- | --- |
| `Host/ApplicationLifecycleBeginOperator.lean` | `057be08bb9dd93f9a7fbc0ed1254cd6d9a03a3195ec2fef037fc2ebc7f3113b6` |
| `Host/Json.lean` | `45ac646ea454706f2ccf3481ce34c8c16c8476a5a3fb096a0a8a696d7808b122` |
| private `Host/ApplicationLifecycleBeginOperator.olean` | `e7f84a8d588a42e264124d8503d464e946082eb1e51ccd681fda1cf835b803d8` |
| private `Host/Json.olean` | `6318cc1e7ad0882f02567137ad9a03bd6f8ca99198f23951b52965346220de6c` |
| private Operator compile log (empty, successful exit) | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| private Json compile log | `004edd44f08ffc0edc5e0420145b64f1315280e1ab347cca66c22238104443a2` |

The private sources and outputs are under `/tmp/minidregg-completion-src/Host/`,
`/tmp/minidregg-completion-olean/Host/`, and
`/tmp/minidregg-resident-begin-{Operator,Json}.log` on Persvati. The shared
sources above were byte-compared by SHA-256 to the private compiled copies.
