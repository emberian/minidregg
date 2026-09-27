# Durable birth controller and work dispatch checkpoint

Mini `ecf81ea` adds controller custody for the actual grain-backed native birth
operation. The operator selects bounded creation families; a model may select
a family name, not replace its factory, payer, template or policy. The journal
consumes an ordinal and retains the birth lifecycle before attach/reserve,
then retains the exact source and pending attempt before submission. Confirmed
receipts enroll the issued grants; uncertainty uses exact native lookup.
Definitive refusal and pre-dispatch interruption preserve zero-charge recovery.

The same change introduces a short spawn/cancel critical section for work-origin
Mini invocations. Hard EOF signals the physical worker before cancelling the
tracked custody child. A veto before spawn is distinguished from an invocation
that may have dispatched. Killing a client cannot undo a call already delivered
to the persistent Host; exact pending state, native lookup and fencing remain
required. Bounded pipe capture and a post-leader drain deadline prevent a child
that retains an output descriptor from blocking the controller indefinitely.

Frozen source SHA-256 identities:

- `main.rs`: `f0f31e12440f107a271d8f06a717fb7eb38f0b26f347946ad1a03a7c45ea0068`
- `resource_tools.rs`: `9f750ff268c9f6f03e6d87733eee5ee274f475d781463d9ad2f83f68d4c7b9e2`
- `custody_gate.rs`: `41449fc36a7906d67c83f7954f16dd21db532449a2b2df0d17920137504e0f8b`
- `birth_lifecycle_tests.rs`: `952007b8ea2497c30cdc1a616c079d5cc1acc9de94610c3d0c526354f009beac`

The isolated crate check ran 59 tests: **59 passed, zero skipped**, in 3.176s.
Formatting and strict all-target clippy passed. Local retained logs are
`/tmp/minidregg-birth-checkpoint-nextest.log` (SHA prefix `65ebf652af8d`) and
`/tmp/minidregg-birth-checkpoint-clippy.log` (`4cf86278c1e6`); root inspected their
verdicts and independently checked the source hashes above. Two independent
source reviewers covered lifecycle ordering and custody cancellation.

The lifecycle tests use controlled Mini-client stubs; they do not prove native
admission. [The separate r3 native birth evidence](../2026-09-26-grain-birth-native/r3/README.md)
establishes the composite kernel operation on its qualified Host. At this
checkpoint, the new runtime has not yet passed a hosted Hermes birth journey,
and the MCP creation tool is not advertised. That integration is active work.
