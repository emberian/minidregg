# Job templates (COMPUTE.md §2, lane C1 JOB-LAW)

A job is a cell with a law; the kernel has no job object. These files are the law.

| file | what |
|---|---|
| `fields.json` | the job cell's field numbers (kind `job`), the state codes, the placeholders |
| `law.job` | **the source**: the law in the templates grammar (`../mud/render.py` dialect, named fields) |
| `law.job.json` | its rendering: the Host's `Pred` JSON, an `all` of clauses 0–44 |
| `law.job.shell` | the same law in the shell's one-line grammar (`native/resource-client/src/shell/law.rs`), each clause spelled as the Host renders it in a refusal |

`scripts/gen-joblaw.py` writes `law.job.json`, `law.job.shell` and `Kernel/Job.lean` §2 from `law.job`;
`--check` fails if any of the four disagree. `Kernel/Job.lean` proves the theorems over §2, and
`law.rs`'s `job_law_grammar_is_the_template_json` parses `law.job.shell` back to `law.job.json`.

**Placeholders** (substituted textually, as `../mud/` does): `{CALLER}` the ordering subject;
`{PROGRAM}` the programId (field `program` is pinned to it); `{WINDOW}` the challenge window in clock
seconds and `{NEG_WINDOW}` its negation. The truth needs K-RAN's `ran {PROGRAM}` (clause 22): the
controller projects `run/program/{PROGRAM}` only for a command whose run claim it re-executed on its
own sample and whose writes are the program's product. The money edges are the job-money receiver's
(clause 44): `mini job --action fund|claim|settle`, ops 160-163.

`programs/` holds the job programs the journeys use (`collatz.hoon`, the job program: input field 2,
truth field 15; `liar.hoon`, a program that names the truth field and answers 9 whatever the input),
compiled by the pinned hoonc (`*.jam.provenance`).

## Fields (`fields.json`)

0 state · 1 program · 2 input · 3 caller · 4 callerAcct · 5 price · 6 claimBy · 7 answerBy · 8 escrow ·
9 provider · 10 providerAcct · 11 bond · 12 output · 13 steps · 14 finalAt · 15 truth.
States: 0 open · 1 claimed · 2 answered · 3 upheld · 4 slashed · 5 void · 6 closed.

Deviations from COMPUTE.md §2.2: no `window` field (the window is the law constant `{WINDOW}`:
`finalAt = clock/now + window` relates three slots, which no atom states with a field-valued window);
`bond` is born `0` so every close can require `escrow = 0 ∧ bond = 0`. Absent fields are absent (a
slot-pair atom on an absent slot is false: `eqSlots X X` is "X is present", `Kernel/Job.lean`
`present_iff`).

## Clauses (the order is the order refusals are reported in; never re-sort)

| # | name | edge | says |
|---|---|---|---|
| 0 | management | every verb | read, write; delegate by the caller only; install and revoke by nobody |
| 1 | state-range | write | state ∈ 0..6 |
| 2 | edges | write | (before, after) ∈ the table, or unchanged; birth enters 0 |
| 3–12 | order-* | birth | caller orders as itself, program pinned, input and callerAcct present, price > 0, now ≤ claimBy ≤ answerBy, born unfunded: escrow 0, and bond, provider, providerAcct 0 |
| 13 | order-fields-frozen | after birth | program … answerBy never change |
| 14 | escrow-frame | | escrow moves only on fund (open, 0 → price) and close |
| 15 | bond-frame | | bond moves only on claim and close |
| 16–17 | provider/providerAcct frames | | born 0 by the order, written by claim, then fixed |
| 18–20 | output/steps/finalAt frames | | absent until answer, then fixed (no second answer) |
| 21 | truth-write-once | | a present truth never changes |
| 22 | truth-needs-ran | truth | `ran {PROGRAM}` (K-RAN: the kernel re-executed the job's program) |
| 23 | truth-in-1-or-2 | truth | state 1 or 2, unchanged |
| 24–26 | truth by provider ≤ answerBy (state 1); anyone ≤ finalAt (state 2) | truth | |
| 27–30 | claim | 0 → 1 | now ≤ claimBy, provider = subject, providerAcct present, price ≤ bond |
| 31–36 | answer | 1 → 2 | by the provider, now ≤ answerBy, output and steps posted, finalAt = now + WINDOW (two `leSlotsOff`), not after the provider's own run |
| 37 | upheld-from-1 | 1 → 3 | the provider's run is on the cell |
| 38 | upheld-from-2 | 2 → 3 | truth = output, or no truth and finalAt < now |
| 39 | slashed-from-2 | 2 → 4 | truth present and ≠ output |
| 40 | slashed-from-1 | 1 → 4 | the stall: no truth and answerBy < now |
| 41 | void | 0 → 5 | the caller any time; anyone after claimBy |
| 42–43 | close | {3,4,5} → 6 | escrow = 0, bond = 0 (the pay-out legs are K-JOB-MONEY's, C3) |
| 44 | money-by-the-receiver | after birth | a write that moves escrow or bond, claims, or closes carries `authority/operation/job-money`, which only the job-money receiver projects |

Every clause but 0 is guarded `not (verb == write)`: a signed read is judged without clock or field
slots. Every deadline is stated positively (`leSlotsOff D clock/now -1` for "now > D"), so a write
without a clock fails closed.

**Not covered**: a write that creates a field outside 0–15 (`Pred` has no "no other field" atom;
`closed_job_admits_undeclared_field`). The amounts (deposit, bond, payouts) are the receiver's
(`Kernel/JobMoney.lean`), checked against the Book; the receiver accepts only a job whose installed
law IS this law at some parameters (`JobMoney.isJobLaw`).
