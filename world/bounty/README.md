# world/bounty

Two packages, two evidence classes.

| file | what it is | evidence |
|---|---|---|
| `BountyBoard.obend` + `preview-cohort.json` | the lifecycle as pure transitions and an Activity whose Plans are PROPOSALS | preview: 19 rows through `tests/objective-bend-source/check-preview.ts`. No kernel holds anything. |
| `BountyEscrow.obend` | the same bounty as a seat contract: the reward is HELD by the seat kernel | executed: `native/resource-client/objective-bounty-native-acceptance.py` on a scratch native world, every turn a signed command (`mini seat`), journey row `bounty` |

## What is native (BountyEscrow.obend)

One instance of the package is one bounty. The contract is stateless and holds no identity; it reads the
open seats it is shown (role, terms, give, want, exit rule, `opened`, allocation) and returns a Plan the
seat kernel judges.

- **Escrow.** The poster's `escrow` seat gives the reward and wants one WORK RECEIPT (an asset the issuer
  mints when the work arrives), or its give refunded. Its exit is `afterDeadline(deadline)`. The poster's
  balance falls by exactly the reward; the seat account is protected.
- **Claim.** The claimant's `claim` seat gives nothing, wants the whole reward, and exits `afterDeadline(due)`
  with `due >= height + review + 1`: it cannot be exited before review ends. The seat is the claimant's handle;
  the kernel pays the seat's payee at exit. First claimer = the claim seat with the least `opened`.
- **Submit.** The claimant offers a `work` seat that gives the receipt. `advance` then performs ONE
  reallocation: reward escrow -> claim seat, receipt work -> escrow. The escrow's own law (receipt or refund)
  judges it.
- **Approve.** The poster offers an `approve` seat (an empty marked donation, `Proposal.donate`); `advance` exits
  every seat: the kernel pays the claim seat's payee the reward whole, once.
- **Reject.** A `reject` seat before `due` makes `advance` swap reward and receipt back; the claim, work and
  reject seats exit; the bounty reopens and the rejected claimant keeps nothing but their receipt.
- **Silence.** No decision: the claim seat's own deadline exit (anyone, at `due`) pays its payee. Silence pays
  the claimant with no activity and no identity.
- **Cancel.** A `cancel` seat with no claim seat refunds the poster. The deadline exit of the escrow refunds an
  unclaimed or rejected bounty.
- **Planted faults** (acceptance rows P): a contract that moves reward+1, one that pays twice, and one that
  moves the reward without the receipt are each REFUSED by the kernel by name (`unfunded`, `unfunded`,
  `offerUnsafe`); roots unchanged. The Book total of gold never changes.

## What is NOT native, exactly

- **"Want = approved work" is not an asset.** The escrow wants a receipt asset instead. The receipt is minted by
  the realm issuer (`mini well`), not by the contract: the kernel enforces "the poster holds the receipt or
  gets the reward back", but NOT that the issuer only mints for work that is any good. The poster's approval is
  still a decision (the approve/reject seats).
- **The poster's decision is a seat, not an activity answer slot.** The decision is the kernel fact "a seat was
  offered from the poster's invitation", read by `advance`. The deadline (`review`) is height arithmetic in the
  contract and the claim seat's exit rule. No ObjectiveActivity is used.
- **Who may decide is invitation custody.** `advance` is callable by anyone holding the instance capability; the
  contract does not know the invoker (held for the grounding round). The approve/reject/cancel invitations are
  minted to the poster at `post`; whoever holds one can decide.
- **First-claimer-wins is by `opened`** (the height of the offer turn). Two claims in one height tie; the tie
  goes to the lower seat coordinate, which is not time order.
- **Activity-held seats.** A seat held by an activity could be pulled early by that activity's end. That was a
  kernel bug (`Seat.exitAuthorized`), fixed by OB-ENG's seat-retention range (`holder_respects_deadline`,
  c4be7c92); this package assumes it, and no row here names an activity holder.
- **Fees.** Each kernel turn pays the declared envelope in the credit asset; the acceptance funds the sponsor
  generously. Not modelled in the preview.

## Re-emits

Depends on the SeatView change (`exit`, `opened`; frame `DREGG/SEAT/SEAT/v4`) and on seat-retention. A seat
package typed at the old SeatView is refused on instantiation.
