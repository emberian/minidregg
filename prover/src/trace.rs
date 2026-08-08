//! `[PROVER-trace]` — trace generation and the descriptor-satisfaction cross-check.
//!
//! `generate_trace` fills the full wire vector: the caller supplies the original
//! variables, the gates (in emission order) define exactly the aux region — the
//! shape `emit_wellFormed` proved of the Lean-emitted descriptor is ASSERTED here
//! per gate, not assumed. `descriptor_holds` is the independent re-check: a literal
//! index-by-index mirror of `Compiler/Emit.lean`'s `descriptorHolds`
//! (`(∀ g ∈ gates, g.holds wv) ∧ (∀ z ∈ zeros, z.read wv = 0)`), sharing no
//! machinery with the generator. That the generated trace satisfies it is a
//! conformance cross-check that RUNS — not a proof about all inputs.

use crate::descriptor::{Descriptor, Fp, Wire};

/// Mirror of `DWire.read` against a finite wire vector. The Lean predicate reads a
/// TOTAL vector `ℕ → F`; here an out-of-range index is `None`, which the checks
/// below treat as failure (conservative reject — cannot arise on a descriptor that
/// passes `validate`, per `emit_wellFormed`).
fn read_wire(wires: &[Fp], w: &Wire) -> Option<Fp> {
    match *w {
        Wire::Const(c) => Some(c),
        Wire::Wire(n) => wires.get(n as usize).copied(),
    }
}

/// Evaluate the descriptor's gates in emission order, producing the full wire
/// vector of length `nWires`.
///
/// `vars` supplies ALL original variables `[0, nVars)`: the public inputs occupy
/// `[0, nPublic)`, the private witness `[nPublic, nVars)`. The gates then define
/// exactly the aux region `[nVars, nWires)` — each gate's output must be a fresh
/// aux wire and its inputs already-defined wires (the invariants
/// `flatten_scoped`/`flatten_covers` proved of the Lean emit; asserted here so a
/// descriptor violating them panics loudly instead of producing a junk trace).
pub fn generate_trace(d: &Descriptor, vars: &[Fp]) -> Vec<Fp> {
    assert_eq!(
        vars.len(),
        d.n_vars as usize,
        "vars must cover the whole variable region [0, nVars)"
    );
    let n = d.n_wires as usize;
    let mut wires = vec![0u64; n];
    let mut defined = vec![false; n];
    for (i, v) in vars.iter().enumerate() {
        assert!(*v < d.p, "variable {i} = {v} not canonical mod {}", d.p);
        wires[i] = *v;
        defined[i] = true;
    }
    for (gi, g) in d.gates.iter().enumerate() {
        let read = |w: &Wire| -> Fp {
            match *w {
                Wire::Const(c) => {
                    assert!(c < d.p, "gate {gi}: non-canonical constant {c}");
                    c
                }
                Wire::Wire(idx) => {
                    let idx = idx as usize;
                    assert!(
                        idx < n && defined[idx],
                        "gate {gi} reads wire {idx} before it is defined"
                    );
                    wires[idx]
                }
            }
        };
        let (a, b) = (read(&g.a), read(&g.b));
        let out = g.out as usize;
        assert!(
            d.n_vars as usize <= out && out < n,
            "gate {gi}: output {out} outside aux region [{}, {n})",
            d.n_vars
        );
        assert!(!defined[out], "gate {gi}: redefines wire {out}");
        wires[out] = g.op.denote(a, b, d.p);
        defined[out] = true;
    }
    assert!(
        defined.iter().all(|&x| x),
        "descriptor leaves wires undefined (no gate outputs them)"
    );
    wires
}

/// Every gate record holds: `op.denote(a.read, b.read) = wires[out]` — the first
/// conjunct of the Lean `descriptorHolds`.
pub fn gates_hold(d: &Descriptor, wires: &[Fp]) -> bool {
    d.gates.iter().all(|g| {
        match (read_wire(wires, &g.a), read_wire(wires, &g.b), wires.get(g.out as usize)) {
            (Some(a), Some(b), Some(&out)) => g.op.denote(a, b, d.p) == out,
            _ => false,
        }
    })
}

/// Every zero-checked wire reads `0` — the second conjunct.
pub fn zeros_hold(d: &Descriptor, wires: &[Fp]) -> bool {
    d.zeros.iter().all(|z| read_wire(wires, z) == Some(0))
}

/// Mirror of `Compiler/Emit.lean`'s `descriptorHolds`: the conjunction of the two
/// checks, read purely by index against one total wire vector. Independent of
/// `generate_trace`. This is the relation `emit_faithful` proved equal to the Lean
/// AIR's satisfaction — checking it here is the conformance cross-check, and only
/// that: Rust has no formal semantics, so this is never verification.
pub fn descriptor_holds(d: &Descriptor, wires: &[Fp]) -> bool {
    gates_hold(d, wires) && zeros_hold(d, wires)
}
