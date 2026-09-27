# Private event20 registration: first native gate

The held r3 recipient was a fresh Mini Store with two empty content resources:
target 600 for the selected release and target 601 for fn progress. The
configured gateway is subject 8, target 601, capability 63. The separately
registered qualified fn consumer `selected-mini-gateway` was at ACK 0,
frontier 2. No selected article had been posted.

The operator used the exact `bf04c29` Linux Host SHA-256
`cf931aae46102755a97920feed13afa36c83ef4d1bfabd2fb17dee1c8bbfa943`
and the corrected `7d03d5e` Linux Mini SHA-256
`5bca4550a0a5b180ed5c78dc49bcf9f650a94afe2488caac1297911ca5c69974`.
The owner-private recipient config SHA-256 is
`0af3d9aec0394458e489aea5f3bf865c97434bc330117a5866a32bbc2bde5205`.
The gateway key is enrolled as subject 8, key ID 8008, epoch 2; its public
key matched the accepted birth enrolment. The key bytes are not included.

Retained private attempt:
`/tmp/mini-selected-fn-recipient-20260927-3/namespace-attempt-1` on Persvati.

| Artifact | Bytes | SHA-256 | Native result |
| --- | ---: | --- | --- |
| `plan.bin` | 730 | `844a6f0a50234439036f953903431bc5b293ff1b2ed52deb32d138db4a55d5ce` | op42 source plan accepted |
| `approval.json` | 1,450 | `0680b885997657eb5e2c3b62e681e7438dc7e5c17935967ed72d28c3ff9e1ebf` | independently matched scope, gateway, enrolled key, and exact plan |
| `assembly.frame` | 800 | `8b156c1ba95e9a07744d734eb61b40bd3ac11bc372d719f31f98b4297f414d2d` | op43 returned ingress |
| `ingress.bin` | 799 | `31b1619cbe22e7101f2863c9e753b02f230948ee867588890577c8e2c5f3befe` | exact source-authored event20 candidate |
| `submit.frame` | 59 | `1546ed0ee5a4faf0c5698eac4aac10a4c5543fe3a4769e4e52f8670833978bd0` | op40 definite admission refusal |
| `lookup-00.frame` | 33 | `d024ce9613cbd878e4ad2e1f5ea997ac9d2b8323aa888b80077bcec304f19136` | op41 exact original absent |

The client wrote `submit-attempt.json` before sending op40 and did not
resubmit after the refusal. Its terminal result was `fn namespace exact lookup
absent; no automatic resubmit`. No event20 receipt, fn ACK, selected POST, or
recipient op20 exists from this attempt. The public refusal is intentionally
generic; source-side read-only diagnosis is pending. The Store and fn node
remain held for that diagnosis.

The preceding plan exposed distinct durable outer and credential logical
authority roots. The operator client correction is in `7d03d5e`; this native
gate ran that corrected binary. This refusal is a separate admission result,
not the earlier client-side root comparison error.
