# Resident service commons

ResidentServiceCommons is an authored world program. It proposes ordinary
state, canonical money and Activity effects; it is not a second execution,
custody or authorization controller.

A request binds an exact method artifact/program/export and input/result
schemas, input digest, context digest, resident home and room roots, recipient,
audience/key epoch, acceptance authority/criterion, dispatch deadline, capacity
units, budget and escrow accounts. An offer binds that same identity, provider
home/capacity root, price and expiry. A sponsorship is an exact bounded spending
endorsement tied to a policy root. It does not certify a provider's advertised
capability or the truth of an answer.

Reservation proposes payer-to-escrow transfer and capacity reservation together.
The native receiver must make both effective with the held request state or
neither. Its source identity and pending native operation are retained before a
provider call. The actual existing public request row uses request cell plus
sequence and assigned Hermes; the native operation identity cannot be replaced
with a fresh retry wrapper.

An uncertain call keeps that exact identity and proposes only observation of
the existing operation. Time passing cannot prove nonexecution. A held,
unstarted reservation can be cancelled by its consumer or expired; a started
one cannot take that timeout refund path. Rejected or late physical work needs
policy-governed reconciliation, not an invented successful cancellation.

Completion must be an independently admitted observation of the native pending
operation. Opaque provider receipt bytes do not establish this. Completion
retention is distinct from recipient acceptance, which matches exact run,
output, acceptance method and reviewer. Only that accepted transition proposes
escrow payout, capacity return and recipient result commitment. Finished state
refuses another payout. Capacity release uses a current admitted home root;
payment uses a current canonical book root.

The single native intent must bind all phase/state, room, Activity, capacity,
book and return changes. Source proposal construction grants no capability.
After-funding account sampling, per-debit current laws and source method/input
identity remain the ordinary native receiver's job.

## Concrete existing joins

- Public resident request rows are native/resource-client/src/hermes.rs
  request_rows, derived from signed chat::room_feed; web/resident.rs consumes
  them. Do not substitute private controller journals for public receipts.
- takeover_service owns physical provider calls, pending-write-before-call
  custody, exact native operation lookup and lost-reply recovery.
- Kernel/BendActivityProgram, Proposal, Ingress and Receiver are the native
  Activity owner; initialization/advance and pending-yield/outcome qualification
  are separate. Source does not fabricate Activity checkpoints.
- Compiler/BendActivityYield.extract reads actual source-produced PlanData and
  captured continuation. The current response ABI is finite false/true. Result
  content stays in separately admitted typed result slots; arbitrary Hermes
  JSON/text injection requires its own typed ABI.
- Before external dispatch, the native pending constructor must reserve enough
  heap capacity to inject the response, validate both Boolean code pointers and
  actual empty environment, and retain exact request-indexed continuation,
  funding/read guards and predecessor.
- ResourceMoneyOperationDomain prepares one validated funding prefix and
  canonical Book batch. Quotes never author their own transfer grant.

ServiceCommonsFaces provides domain, source and Activity faces over the shared
WorldSurface. Quote, provider claim, sponsor decision, completion and recipient
review occupy distinct admitted observation rows. Exact source origin and
prepared native intent bindings are required for action nodes. Same Activity
link survives uncertainty and delivery. The resident home and request are
ordinary admitted object/document mounts; source code is inspected through the
same Studio, not an untrusted renderer script.

Current source packages are published before remaining checks. Source, actual
BendTT Book checking, typed source-to-native effect adaptation and native
receiving must each report their own result. This contract serves research
reviews, authored tools, world participation and service exchange. It does not
turn every resident action into a paid numeric market or assert current private
execution supports arbitrary model/provider tasks.

