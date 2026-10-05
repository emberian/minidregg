# Seats and invitations

Offer safety as a law over the Book: a **seat** is a Book account that holds one party's side
of a contract, judged by a decidable law on every change to it, with an exit no contract can
forbid. An **invitation** is the single-use, assayable right to play one role of one contract
instance (Agoric Zoe's invitation and `isOfferSafe`; Miller, Van Cutsem and Tulloh, ESOP 2013
§6). A contract is an Objective Bend package; the overview is
[OBJECTIVE-BEND.md](OBJECTIVE-BEND.md#seats).

Modules: `Kernel/Seat.lean` (the seat world, its one transition function, invariant and
theorems), `Kernel/Invitation.lean` (the pure invitation rules), `Kernel/SeatStore.lean` (the
world in stored cells and the turns), `Kernel/SeatCell.lean` (protected coordinates),
`Kernel/SeatReceiver.lean` (the signed route), `Kernel/ActivitySeatEnd.lean` (an ending
activity closes the seats it holds). **Integrated on scratch worlds**: Host operations 215-219
(plan, assemble, submit, lookup, view), `mini seat`, driver
`native/resource-client/objective-seat-native-acceptance.py` (rows E1-E9), journey row `seats`.

## Invitations

An `Instance` is a contract instance, its package identity and the contract's own clause (a
`Pred`). An `Invitation` has an id, instance, package, role, terms the holder can read, and one
holder. `mint` happens only in a turn of the instance it names, carrying that instance's own
package, under a fresh id; `handOver` is the holder's; `spend` requires the holder to present
it and it to match the holder's `Expectation` (instance, package, role: the assay), and moves
the id to `spent`. Theorems: `spend_once`, `spent_not_live`, `spent_never_minted`,
`spend_result`.

## Seats

A `Seat` is a fresh Book account at a protected coordinate (`seatAccount_protected`; the
offerer never names it), with its instance, offerer, payee, an optional holding activity,
`Proposal {give, want, exit}` and an open flag. The law is `offerSafe proposal`: every `want` is
met, or every `give` is refunded, as a `Pred` over a total view of the seat's balances, so an
absent slot is never what the law sees (`view_total`; `absent_slot_reads_as_met`,
`zero_want_satisfied`).

Turns (`SeatStore.Turn`), each a signed native command:

| Turn | Who | Rule |
| --- | --- | --- |
| `publish` | the package's payer | stores a contract package after the front end's replay |
| `create` | a holder of the instance object | instantiates a published package as a contract instance |
| `handOver` | the invitation's holder | moves the invitation |
| `offer` | the owner of the funding account (and, naming a holding activity, its payer while it awaits) | spends the invitation, opens the seat, posts `give` into it; refused unless the seat already satisfies its law |
| `invoke` | an instance object holder paying the envelope | runs the instance's own package method on the canonical view of its open seats and performs the Plan it returns: reallocations, mints, contract exits, termination |
| `exit` | the offerer on demand, anyone after the deadline | pays the seat's whole allocation to its payee and closes it |

There is no signed `reallocate` or `mint`: they exist only as members of the Plan the instance's
code returns when the receiver re-executes it (`reallocate_requires_instance_holder`). A
reallocation must be admitted by the contract's clause, move value only between open seats of
that instance (credit only in an asset the receiving proposal names), and leave every touched
seat satisfying its law. The signed header commits to the decided turn's posts, so a Plan that
changed between signing and submission is refused, never settled differently.

**Exit.** `exitAuthorized`: the offerer of an `onDemand` seat at any height; the seat's own
instance; the activity holding the seat; anyone once an `afterDeadline` seat's due height is
reached. The exit path never reads the contract's clause, so no clause can forbid an exit.

## What is proved

Over the invariant `Inv` (open seats satisfy their law and hold non-negative balances; seat
accounts are registered, distinct, protected, and not their own payee):

- `step_inv`: every admitted step preserves `Inv`; `seat_offer_safe_forever`: from a world with
  no seats, every open seat of every reachable world satisfies its law (premise inhabited by
  `swap_opening_reachable`).
- `exit_admitted`, `exit_enabled`, `exit_after_deadline`, `exit_by_holder`: a party with exit
  rights is admitted at every reachable world; `exit_pays_allocation`: afterwards the seat is
  at zero in every named asset and the payee has gained exactly its balance.
- `seat_conserves`: every admitted step conserves every asset; `seat_debit_authorized`: an open
  seat is debited only by its own instance's reallocation, by an exit, or by its instance's
  termination.
- `activity_end_closes_seats`, `Joined.closes`, `Joined.conserves`: an ending activity closes
  the seats it holds in the same Book batch, conserving.
- Receiver: `native_turn_is_kernel_turn`, `native_invariant_preserved`,
  `native_turn_conserves`, `intent_writes_seat_or_book`, `offer_requires_account_holder`,
  `exit_requires_offerer_or_deadline`, `native_offer_spends_invitation_once`.
- Teeth: `swap_settles_after_price_move`, `raid_refused`,
  `locked_contract_refuses_reallocation`, `locked_contract_cannot_stop_exit`,
  `stranger_cannot_exit`, `invitation_spent_once`, `assay_refused`,
  `unprotected_seat_refused`, `zero_want_gift_admitted`, `activity_end_pays_held_seat`,
  `another_activity_ends_nothing`.

## Limits

- The contract clause is evaluated on the constant state `requestState 1`: a fixed gate on
  whether an instance may reallocate at all, never a judge of the transfers. The judges of a
  reallocation's content are the seats' own laws.
- `Inv` constrains open seats only.
- No theorem states that termination leaves every seat of the instance closed; it is read from
  the code.
- Amounts are fungible only; there is no set-valued amount.
