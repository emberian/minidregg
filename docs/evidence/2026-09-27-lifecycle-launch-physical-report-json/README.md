# Launch physical report v2 JSON routes — source gate

The Host JSON boundary now authors three distinct v2 artifacts using the
source-owned `ApplicationLifecycleLaunchReportAuthoring` helper:

| Kind | Exact input fields | Output |
| --- | --- | --- |
| `application-lifecycle-launch-physical-report` | `begin`, `committedClaim`, `nonce`, `unit`, `materializedImage`, `outcome`, `invocationId`, `controlGroup`, `pid`, `stopAudit`, `volumeWitness` | Canonical physical report v2 |
| `application-lifecycle-launch-physical-signing-frame` | `begin`, `report` | Exact physical-custodian signing frame, with domain and semantics derived from BEGIN |
| `application-lifecycle-launch-physical-signed-report` | `begin`, `report`, `signature` | Canonical signed report v2; detached signature is exactly 64 bytes |

Binary fields are hexadecimal strings and unsigned integers are canonical
decimal strings. `stopAudit` is null or an exact typed object; `volumeWitness`
is null or hexadecimal witness bytes. The report helper derives the volume ID,
installed manifest, and claim binding. The corresponding report and signed
report `inspect` kinds strictly decode the v2 codecs and echo canonical bytes
and typed fields. Inspection is presentation, not physical attestation or
admission. Host.Main bounds these author inputs and inspect outputs.

Source pins:

| File | SHA-256 |
| --- | --- |
| `Host/ApplicationLifecycleLaunchReportAuthoring.lean` | `0ad8843b47e6dce93edd3a22db402743b1b90016271a0d942e15aafe3f11aead` |
| `Host/Json.lean` | `a385a13b6b50d98053d4a70200026a0e7dcf89406c7fa9dac2da057aab155560` |
| `Host/Main.lean` | `9dbe268baaec650ec0d753258e5b59c91d5a2f6c2622bebb6adb46b43a988c06` |

On an independent writable hbox overlay over the source-qualified 55d3868
prefix plus committed lifecycle Replay/CAS imports, serial direct Lean
compilation of helper, Json, and Main exited 0. Helper and Main logs are empty;
Json reports existing linter/axiom notes. Json OLean SHA-256 is
`7569a4bd72ed2a8ad9714c4f929665e26bf13ef81a29f21ea311eaf61419483c`;
Main OLean is
`9efe4b72117f1578809632c496e77131308a717dbcf06ec1937f382994d7e5da`.
The bounded diagnostic refusal probe exited 0 and returned `true` for all
five malformed/wrong-family cases, recorded in
`minidregg-launch-report-refusal.log`. These are component checks; no linked
native Host or physical report was accepted by this gate.

The current STOP author still names a new-generation unit. A truthful STOP
against the prior running unit remains closed until the verifier-selected
prior-running identity repair qualifies. This report helper itself does not
disable STOP; native and physical custody must enforce the corrected source.
