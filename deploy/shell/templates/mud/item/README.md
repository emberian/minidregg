# item: the MUD unique-item law

`law.item` is the source, and `law.item.json` is rendered by `../render.py`. The installed law is
`law.management ; law.item [; law.item-reward]`. Clause numbers are composed indices, and new clauses are
only ever appended.

## Two gives from one pre-state: the law is per-step, and ordering belongs to the CAS

SHEET-ITEM-LAW proved `concurrent_gives_both_law_admitted`. The holder's `give → B` and `give → C`, each
judged against the same pre-state (owner = holder), are **both** admitted by this law. `sim.py` J-MUD-2 r4 and
r4b show the same thing. This is intended, not a gap in the law:

- A cell law is a predicate over one step's `(old, new)` projection. It cannot see a second transaction, so no
  clause can tell "the other give landed first" apart from "there is no other give".
- The refusal of the second give is the durable stale-read guard. Each `give` is sent as
  `write owner NEW expected OLD`, and the store refuses a write whose `expected` is no longer current
  (`guardFailed`; `DurableDataIntent.stale_read_guard_rejected`). That check runs before any law.
- Once the first give has landed, the law also refuses the second one on the new pre-state
  (`second_give_refused_after_first`; `sim.py` J-MUD-2 r4c, clause 1 holder).
- So `no_dupe_unique` is stated over **chained** steps: an accepted log in which each step's pre-state is the
  previous step's post-state. That chaining is the CAS's guarantee. It is not derived yet. Deriving it from
  `DurableDataIntent`'s guard is the open item in SHEET-ITEM-LAW's "what is not done" list.

Why this is not the alternative, "add an `expected` guard to the law": the projection has no `request/expected`
slot (`CanonicalRuntimeProfile.lean:120-132`, `requestSlots`: kind, verb, subject, subjectKeyEpoch, federation,
height, policyEpoch, policyRevision, nonce, target, policyId, cost). Even if it had one, both concurrent gives
carry `expected = owner/before` against the same pre-state, so such a clause would admit both, exactly as
clause 1 does. MUD §2.2's `owner writeOnce` would not help either. A same-value rewrite passes `writeOnce`
(p-templates §2.8 item 3), and a `writeOnce` on a non-zero owner would refuse **every** give.
