# Accepted B/A historical selector replay

The read-only Lean probe [`scripts/probe-fn-accepted-history-selectors.lean`](../../../scripts/probe-fn-accepted-history-selectors.lean)
reopened the completed, independent B and A Mini Stores through
`NativeHost.openExisting` under the coherent next-source snapshot
`/tmp/minidregg-overnight-20260926-next` (committed full-command selector
`5958e5b` and session `ee629b1`). It required exactly one B
`FnConsumerOperation.originalBindingWithInbox` and one A
`FnReplyConsumption.originalResult` match in their accepted histories.
The [captured stdout/stderr](accepted-history.log) reports **PASS**, with two
accepted records in each Store. No fn poll, ACK, submit, or Store mutation
was performed by this probe.

SHA-256 manifest:

| Input | SHA-256 |
| --- | --- |
| Probe source | `b41e0bd3712056571f6addcc46e67d563912cde63dd2ee241b0c99b752fe7801` |
| `Kernel/FnConsumerOperation.lean` | `b052762104d2545c22253531fc7b98e7fe4eb92733ca70a7dd11abeed74237b8` |
| `Kernel/FnReplyConsumption.lean` | `9d4ada41fd2c6c7d290c12b43a53c49ca57356b592ad2f6775501be17ba7fcd0` |
| `Kernel/FnConsumerProgress.lean` | `c151ad9b08d3be5cfaed262412904423439768f4b533a4c41fe1fe8a05f46e9e` |
| Completed B config | `4420a5ff47a288cdc86922679247e7e1b1ffa36e55c5adce981fc70d3b15ee92` |
| Completed A config | `8d17c56b84b53706d49b6aa3082170e8db18753750781520df9896f812ad4211` |
| Coherent linked host | `b9ff9832b13ad67124e753ab52122732bfe9b795653e2ba64c1e0f35b051ee8a` |
| Captured log | `edc14af97c360db6767ea66bffced8a032681de2e58623eb613997396113ab2f` |

The private B and A configs were read from
`/tmp/mini-fn-final-ab-bbf-20260926-retry/run/mini-b/config.json` and
`/tmp/mini-fn-final-ab-bbf-20260926-retry/run/mini-a/config.json`; their
contents are not copied here. This is a selector continuity check against
previously accepted events, not a new fn Store acceptance claim.
