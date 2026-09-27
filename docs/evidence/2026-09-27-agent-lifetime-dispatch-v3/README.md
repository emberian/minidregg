# Grant-bound event26 reserve context — source check

This is a source-only refinement of event26 before any native event26 route or
accepted event26 history. The event26 ingress frame remains `v1`; its field
schema now carries a distinct `v3` reserve context. Event21's ingress, reserve
context, reserve nonce, payer nonce, and historical receipts are unchanged.

The signed reserve and current payer command use distinct v3 nonces derived
from the complete canonical v3 context. That context commits the exact grant
resource, Replay-certified event27 issue index, digest of canonical grant bytes,
original event22 ticket/session coordinates, current parent and purse
generations, request digest, and charge ceiling. The event26 reserve claim
retains event21's receipt-based nullifier namespace, so one accepted reserve
receipt cannot be consumed once under each version. The candidate intent adds
current signed app, manifest, enrollment, ticket, grant, and purse read guards.
The grant's complete physical content root is compared with the certified
event27 post root; current policy and capability are checked afresh, rather
than pinned to their issuance revision.

The lower component cannot by itself prove that an event22, event27, or purse
reserve occurred in the verified chronological image. Upper Replay must mint
those historical witnesses and bind all three to this exact event26 ingress
before native receiving is exposed. There is no Host op, runtime permit, or
native acceptance result in this checkpoint.

## Source and compile identity

An independent writable overlay on hbox at
`/tank/dregg-build/mini-lifetime-grant-review-20260927` imported the immutable
exact-55d3868 prefix-292 copy. Prefix manifest SHA-256:
`0c0b8fd0aedf4f97650d3ad4d369629e955943fd472c0ec089eb4de0f017d1cd`.
The six owned files were copied from the shared tree and compiled serially,
each with `LEAN_NUM_THREADS=2 lake env lean -o
.lake/build/lib/lean/Kernel/<name>.olean Kernel/<name>.lean`, in the order below.
All six commands exited 0; each captured compiler log is empty. The hbox seat
was acquired atomically and released by an EXIT trap. No prefix artifact or
shared native build tree was modified.

| Module suffix | Source SHA-256 | OLean SHA-256 |
| --- | --- | --- |
| ReserveContext | `39b222751af242c84d0ba3f94ab8f07c389dbe7f93ea52354810712f876c8a70` | `2feb8a6a09d55d69edecaea8f5ef84cea9e0393764076633f3fb1fddeedebd6c` |
| ReserveCore | `9bc8507467982f004a0461dd5e425e208ce024ab835823edab4c287c36ad9d7d` | `7f1576da04ba2cfec822fe4f4174dac68a46c115c7b645762555c7c0cd796e65` |
| Payer | `2f02d9692f247b471e0002e51bb598bf4ac6207ae4e5c4564b723c38e48c67d8` | `dfcdb577ce1f42b2f2e310ae6fcbb96bd14276c689216ef4eb36b5b3c9b6bbd4` |
| Ingress | `5bf5a50c6984977bbaf6ef82e22b14669e26f17a90e5280d80940fe58d6e30db` | `d1294b5530f6953d94d62229e48428c04f3fc7ba50966ce9f4f52b5b58c5cb6b` |
| Current | `3352804b8d0ad919d3c43bd5c34d10b1981fa9b4e20b5a3f1b89e2632db09e20` | `ec5117b6e276d2dc4ba88921ba54c54d517b65a389ef19605a8034d2dfd79914` |
| Core | `cf1521c4f37588ef2bbd31c663f085b41ecb0ecd19cf25d1bdef927f428644e7` | `ce2a1d921e90c4931e2a0c609d4c490a91a27c9d674a1ea341c626f6dfa10867` |

The source paths are `Kernel/ApplicationAgentLifetimeDispatch<suffix>.lean`.
The six empty per-module logs have SHA-256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
The captured [axiom output](axioms.log) has SHA-256
`245ac933e77c427d8df718053b2177a04300d40ef5672681bab37aef0ad16fa3`;
the named codec, grant-match, read-guard, and event-version theorems report
only `propext`, `Classical.choice`, and `Quot.sound`.
