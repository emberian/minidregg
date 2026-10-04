# world/dues — standing dues and prepaid leases for rooms

`StandingDues.obend` + `preview-cohort.json` (49 rows). Evidence class: **executed in the
effect-free preview** (`tests/objective-bend-source/check-preview.ts`); not native.

## What it does
A payer owes a room `amount` every `period` heights from `start`, for `periods` periods.
Period k falls due at `cursorAt(k) = start + k * period`.
* **Once, in order.** A discharge names the period it pays; only the period at the cursor is
  accepted, once `now >= cursorAt(k)`. A replay (behind the cursor) and a skip (ahead) are
  refused; nothing pays early. Anyone (a keeper) may discharge; the transfer is always the
  committed payer to the committed room for the committed amount.
* **Catch-up pays each missed period once.** Three periods overdue means three discharges,
  three payments, never four (`DuesCatchUpStopsAtDue`, `DuesActivityCatchUpPaysThreeNotFour`).
* **Cancel.** The payer alone, only inside the notice window at the boundary of the next
  unpaid period (`cursorAt(k) <= now < cursorAt(k) + window`) and never while in arrears.
  Mid-period, past the window, by a stranger, or while behind: refused.
* **Prepaid lease** (`lease: true`): the payer deposits up front; each discharge draws from the
  deposit in the same step that advances the cursor; a short deposit refuses the draw and `lapse`
  ends the lease; `settle` refunds the unspent balance to the payer once. `top-up` only by the
  payer. Law `duesLaw`: paid = k * amount, and deposited = held + paid + refunded.
* An activity `dues(terms, deposit)` yields `await{phase, period, due}` and `pay{from,to,amount,
  escrow}` Plans and is resumed with typed events or kernel acknowledgements. A refused
  transfer leaves the period owed.

## Cohort
Happy path (on time, full term, lease draw, lapse, settle, top-up); refusals: early, double
trigger, skip, after term, cancel mid-period / by stranger / past window / while behind /
after cancel, lease short, early lapse, double settle, settle while running, top-up by a
stranger or on pay-as-you-go, void terms; the law over seven account shapes; ten activity runs.
Teeth (run against the cohort, each red; logs kept in the lane): dropping the cursor check
(`d.period == a.k`) turns `DuesSkipRefused` red; dropping the cancel notice window turns
`DuesCancelMidPeriodRefused`, `DuesCancelPastWindowRefused` and an activity row red; a wrong
`expected` (`DuesFullTermPaid` 41) turns its row red.

## What Bread had
`Deos/StandingObligation.lean` (cursor, `cursor_strict_mono`, `replay_rejected`,
`behind_schedule_rejected`), `Deos/PrepaidLease.lean` (meter and draw fused), and
`starbridge-apps/subscription` (seeded; a cap-grant queue, not a payment schedule). Bread's were
theorems over a 1-felt heap root; here the same laws are checked on cohort instances only
(no theorem is claimed: closed instances, not a proof of the general statement).

## Not yet native
No seat, no Book posting, no height await exists for this package: the `pay` Plan is a proposal.
The native route is the activity route (an Activity that awaits `height{at: due}` per period,
object record R2) plus SEATS-NATIVE (the payer's seat as the source of each transfer, the lease
as an escrow seat). Times are caller-supplied `now` fields standing in for the kernel's height.
Front-end note: the typed-argument encoding has no sum values, so the entry takes scalar `Terms`.
