# Fixed-access Objective Bend controller

This construction lowers the actual `BendClosureMachine` microstep to the shared
Boolean `ObliviousNetwork` DAG. It is not a replacement interpreter. The public
profile fixes the checked source Book/template, its compiled ROM, heap slots,
continuation/argument capacities, pointer width, source-count width, and tick
budget. Input values belong in the separately admitted private environment.
Compiling a selected secret literal into this public ROM would disclose it.

All twelve controls are authored: evaluate; ordinary and walk-resume lookup;
return; application; unspine; walk; classify; complete; refused; reverse and
install arguments. Every block receives the same initial state. Their selected
outputs are combined, never chained: chaining could accidentally execute two
source-machine ticks when a control changes. Heap/table access scans every
public row, and writes have the same fixed shape. Allocation, frame capacity,
backward-pointer checks and first-error precedence remain actual circuit gates.

`BendObliviousMutation.Trial` models a microstep transaction. On source refusal,
its final selector retains the complete original state except the refusal
control. This does **not** restore physical preprocessing material: all rows in
the source-authorized fixed public circuit allocation stay burned. Completion
and refusal remain absorbing machine states but still run the full circuit for
the remaining public tick budget.

The DAG output is `handled :: packedStateBits`. A false handled bit means the
physical transition must not be accepted. In particular source-counter carry
returns the original state with handled=false instead of wrapping the private
counter. Source counts are not public charges, refunds, timing, or activity
metadata. `BendObliviousExecution.runReference` retains every per-tick status
wire; it is a clear test consumer. A real private release predicate over these
wires needs its own exact counted circuit and correlation allocation.

The packed codec validates the fixed shape and word ranges, and reverse mode
also checks the combined argument-buffer length. Recursive captured-environment
readiness and cache certification remain stronger semantic prerequisites than
merely decoding a state. The public compiled ROM retains exact source/compiler
correspondence. Private code would additionally require an in-circuit binding
to the admitted source commitment; this public-ROM profile does not provide it.

Qualification is deliberately layered:

- The source closure machine, source compiler, and packed input loader have
  independent qualified checkpoints.
- Fixed controller modules and finite actual-DAG/actual-machine conformance are
  being checked incrementally. The probe reports exact mismatches and the
  emitted graph census; examples do not prove all-program equivalence.
- General builder preservation, graph forcing, codec conformance, source
  reachability and controller simulation must compose into the general theorem.
- Malicious coherent input sharing, checked triples, authenticated multiplication,
  holder-private successor output, and durable recovery must consume this exact
  circuit. Neither a clear circuit evaluation nor a one-use row receipt proves
  that private backend security.

`Prepared` binds the actual compiler result and exact network producer. Native
receiving still checks current source authority, exact invocation/input/output
semantics and release authorization. A serialized digest or an externally
provided success Boolean is not a substitute for these constructors.

## Qualified controller checkpoint (2026-10-03)

All controller modules now compile. The actual probe passes 64/64 one-tick
source-machine comparisons, including rollback after the second allocation or
second frame push fails. Named `#assert_compiled` gates record this finite
compiler-trusting evidence and counter-overflow refusal. For the public test
profile (8 heap rows, 4 frames, 4 arguments, 5 pointer bits, 8 counter bits,
19 ROM instructions), the emitted network has 309 input bits, 310 output bits,
81,250 gates, 32,815 AND gates, 46,903 XOR gates, total depth 119 and AND depth 37.
This is one tick of the unoptimized circuit, not an MPC throughput claim.

Raw output state is deliberately not canonical source reencoding: inactive
union fields and unused padding may retain prior bits. Multi-tick execution
feeds these raw bits directly forward. The correct refinement relation is
successful decoding plus the reachable packed-state invariant, not equality to
the canonical encoder output. A separate admitted-source fixed-network consumer
is being qualified to exercise this full physical pipeline.
