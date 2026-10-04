# Seats and invitations

Offer safety as a law over the Book: a **seat** is a Book account that holds one
party's side of a contract, judged by a decidable law on every change to it, with an
exit no contract can forbid. An **invitation** is the single-use, assayable right to
play one role of one contract instance (Agoric Zoe's invitation and `isOfferSafe`;
Miller, Van Cutsem and Tulloh, ESOP 2013 §6).

**Evidence class: compiled and proved in Lean, not integrated.** The model is
[Kernel/Seat](../Kernel/Seat.lean) (one transition function, invariant and theorems) and
[Kernel/Invitation](../Kernel/Invitation.lean) (the pure invitation rules). Neither is
in the Host closure (`scripts/gates/host-closure.pin` has no `Kernel.Seat` or
`Kernel.Invitation`; `Kernel.lean:58` imports `Kernel.Seat`), no Host operation, `mini`
verb or `.obend` program emits a seat action, and no journey runs one
(`scripts/pipeline/journey-rows:80-91` finds no seat driver). Activities do not yet hold
seats (`Kernel/Seat.lean:29-32`). In flight: SEATS-NATIVE. Line numbers are for main at
4795b657.

## Invitations

- `Instance` (`Kernel/Invitation.lean:28`): a contract instance, its package identity and the
  contract's own clause (a `Pred`). `Invitation` (`:34`): id, instance, package, role,
  terms the holder can read, and one holder.
- `mint` (`:73`): only by a turn of the instance the invitation names, carrying that
  instance's own package, under a fresh id (never live, never spent).
- `handOver` (`:84`): only the current holder changes the holder.
- `spend` (`:109`): the holder presents the invitation and the invitation must match the
  holder's `Expectation` (`:95`: instance, package, role, "the assay"); the id moves to
  `spent`. Proved: `spend_once` (`:144`, a second spend is refused as missing),
  `spent_not_live` (`:134`), `spent_never_minted` (`:153`; its conclusion is only "some
  refusal"), `spend_result` (`:120`).

## Seats

A `Seat` (`Kernel/Seat.lean:395`) is a fresh Book account with its instance, offerer,
payee, `Proposal {give, want, exit}` (`:51`) and an open flag. `step` (`:490`) is the one
transition function of the seat `World` (`:404`: Book, account owners, invitation registry,
seats); its seven actions:

| Action | Rule |
| --- | --- |
| `create` | a subject registers a contract instance |
| `mint`, `handOver` | the invitation rules above, by an instance and by the holder |
| `offer` | spends the invitation, registers a fresh unowned account for the seat, posts `give` from the offerer's own funding account into it, installs the seat; refused `offerUnsafe` unless the seat already satisfies its law |
| `reallocate` | an instance turn of the named instance only: the contract's clause must admit it, every transfer must be between open seats of that instance (credit only in an asset the receiving proposal names), then every open seat the transfers touched must satisfy its law (`firstUnsafe`, `:471`) |
| `exit` | pays the seat's whole allocation to its payee and closes it |
| `terminate` | an instance turn: closes every open seat of the instance, then retires the instance and spends its live invitations |

**The law.** `offerSafe proposal` (`:70`): every `want` is met, or every `give` is
refunded. It is a `Pred` over a total view of the seat's balances (`view`, `:75`: every asset
the proposal names has a slot, so the fail-closed reading of an absent slot is never what the
law sees; `view_total`, `:92`). A zero amount is the empty conjunction (`atLeast`, `:65`), so
"want 0" is met and an empty-`want` seat is always safe.

**Exit.** `exitAuthorized` (`:451`): the offerer may exit an `onDemand` seat at any height;
anyone may exit an `afterDeadline due` seat once `due ≤ height`; an instance turn of the
seat's own instance may always exit it. The exit branch of `step` (`:550`) never reads the
contract's clause (only `reallocate` calls `contractAdmits`, `:480`, `:540`), so no clause can
forbid an exit.

## What is proved

All in `Kernel/Seat.lean`, over the `Inv` invariant (`:568`: open seats satisfy their law and
hold non-negative balances; seat accounts are registered, distinct, unowned and not their own
payee), unless noted. Statements read; `#assert_axioms` pins the main theorems (`:1211-1213`) and the teeth
(`:1379`); the remaining lemmas are compiled without a pin.

- `step_inv` (`:815`): every admitted step preserves `Inv` (parts: `offer_inv` `:730`,
  `reallocate_inv` `:785`, `closeSeat_inv` `:631`, `closeAll_inv` `:660`).
- `seat_offer_safe_forever` (`:924`): from a world with no seats, every open seat of every
  reachable world satisfies its law. The premise is inhabited (`swap_opening_reachable`, `:1371`).
- `exit_admitted` (`:931`), `exit_enabled` (`:945`), `exit_after_deadline` (`:951`): a subject with
  exit rights is admitted at every reachable world; the on-demand offerer can always exit.
  `exit_pays_allocation` (`:959`): afterwards the seat is at zero in every named asset and the
  payee has gained exactly its balance.
- `seat_conserves` (`:978`): every admitted step conserves every asset.
- `seat_debit_authorized` (`:1071`): an open seat is debited only by its own instance's
  `reallocate`, by `exit`, or by its instance's `terminate`.
- Teeth, decided by `decide +kernel`: `swap_settles_after_price_move` (`:1290`), `raid_refused`
  (`:1295`), `locked_contract_refuses_reallocation` (`:1308`), `locked_contract_cannot_stop_exit`
  (`:1312`), `stranger_cannot_exit` (`:1317`), `invitation_spent_once` (`:1322`), `assay_refused`
  (`:1327`), `zero_want_gift_admitted` (`:1356`).

## Limits to know before relying on it

- The contract clause is evaluated on the constant state `requestState 1` (`:477-481`): it
  is a fixed gate on whether an instance may reallocate at all, and never sees the transfers.
  The judge of a reallocation's content is the seats' own laws.
- `Inv.safe` constrains open seats only; a closed seat is unconstrained.
- An `afterDeadline` seat cannot be exited by its offerer before `due`; an instance turn of
  another instance cannot exit it even after `due` (the instance arm of `exitAuthorized`
  matches first).
- No theorem states that `terminate` leaves every seat of the instance closed: `closeAll_inv`
  and the conservation lemmas hold, the closure of each seat is read from the code.
- Fees, non-fungible (set) amounts and the native route are absent (`Kernel/Seat.lean:29-32`).

The invariants above are about this model's own `World`. Joining it to the Book cell, the signed
route and activity abort (an aborted activity must call `closeSeat` for each seat it holds) is the
SEATS-NATIVE lane's work.
