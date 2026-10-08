# Commission Board — D1

A native composition: a guild posts a paid commission, a fleet object claims and
submits under the poster's scoped grants, a reviewer answers through `call`, and
the seat kernel holds and pays the reward. One Board object is one commission;
`list` returns its complete state. The driver posts three objects and registers
each with the same Guild object in a native invariant domain.

| Package | Composition and enforced law |
| --- | --- |
| Board + Protocol | Reward and claimant are writeOnce; cancellation requires no claimant; submission requires a claim; approval requires submission. |
| Agent + Protocol | Calls Board through a grant bound to target, method, package pin and this caller; `units` is cumulatively capped. Its call counter is monotone. |
| Review + Protocol + CatalogReview | A synchronous callee uses the existing exact-candidate and policy check; a stale work revision returns zero. Review revision is writeOnce and endorsement is a bit. |
| Guild + Protocol | Member identity is writeOnce. Each Board/Guild domain requires an unclaimed board or its active member as claimant. Deactivating that member while claimed is refused. |
| Escrow + BountyEscrow + NatOrder | The existing seat contract: reward against a WORK RECEIPT asset or refund, paired claim/work invitations, approval and deadline exits. |

Run the native driver with a fresh, short root (Unix socket path limits apply):

```sh
python3 native/resource-client/commission-demo-journey.py --bin /path/to/bin --root /tmp/cb-new
bash scripts/kn2/plant-commission-double-pay.sh /path/to/bin /tmp/cb-plant-new
```

The standing pipeline row is `commission`. Missing binary inputs alone return 98;
source, admission or assertion failures return failure. `results.json` contains
all checks, pins, mutation hashes and Book totals; `receipts.json` contains native
turn outcomes; `groups.tsv` supplies pipeline subrows; `transcript/` preserves
commands and their outputs. Source publication and replay use the Lean front end,
as in the native bounty journey; no separate Lean model substitutes for admission.

- **CB1:** post and list, reward rewrite refused (`writeOnce`), capped agent
  claim/submit, receipt exchange, reviewer call, poster approval seat, claimant
  paid exactly once; a second exit is refused `seatMissing`.
- **CB5:** unclaimed cancellation refunds the poster; cancellation after claim is
  refused by the Board's package law (`lawDenied` with cancelled/claimant leaves).
- **CB7:** no reviewer invocation or approval seat for this commission; before the
  deadline exit is refused `exitNotAuthorized`, at the deadline it pays the
  claimant, and another exit is refused `seatMissing`.
- **CBP:** the captured BountyEscrow source is mutated to request the reward twice
  in one reallocation. The exact mutation is asserted, separately published and
  invoked; native admission must refuse `unfunded`, preserving roots and balances.
- **Book:** the total of the reward asset is unchanged across all observed turns.

## Composition boundaries

Board writes and seat turns are distinct signed operations, not one atomic
transaction. The driver coordinates them and observes the native results. Board
is an index, not the ledger: rewards only move through the seat kernel. Capped
grants authorize the nested Board claim/submit calls; they do not authorize seat
invocation or transfer the poster's approval invitation. The poster observes the
review result and separately offers approval. The existing escrow itself ignores
cancel seats after a claim; the named cancellation refusal is the Board law.

The fleet here is a pinned Agent object executing authored call logic, not a
hosted external agent runtime. The realm issuer mints the WORK RECEIPT asset;
receipt issuance is an attestation that work arrived, not kernel proof of its
quality. CatalogReview checks the candidate revision and policy, while the
reviewer's stored endorsement supplies its decision.

Guild uses permanent native invariant-domain membership. Required exits at
registration have no representation in the current kernel and are a separate
kernel task; this package does not promise an exit or recovery bypass.

## Runtime dependency

D1 requires the train-kern charged-refusal codec fix (`8e37e22d`, StoreEpoch v6).
With artifact set `0ea31db5`, package-law charged failures exceeded the native
600-second response deadline (job `j497146824`); those uncertain replies are
failures, not named-refusal evidence. Run against the fixed kernel with a fresh
Store. The exact-tree umbrella build and the runtime artifact qualification are
separate evidence.
