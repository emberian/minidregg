//! Candidate trace computation from a Lean-emitted gate buffer.
//!
//! This module returns data only.  It contains no descriptor-satisfaction or
//! acceptance predicate; generated Lean control checks the returned wires.

use crate::descriptor::{Descriptor, Fp, GateOp, Wire};

/// Evaluate the descriptor's gates in emission order, producing the full wire
/// vector of length `nWires`.
///
/// `vars` supplies ALL original variables `[0, nVars)`: the public inputs occupy
/// `[0, nPublic)`, the private witness `[nPublic, nVars)`. The gates then define
/// exactly the aux region `[nVars, nWires)` — each gate's output must be a fresh
/// aux wire and its inputs already-defined wires (the invariants
/// `flatten_scoped`/`flatten_covers` proved of the Lean emit; asserted here so a
/// malformed work buffers stop native computation instead of producing data).
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
        wires[out] = match g.op {
            GateOp::Add => ((a as u128 + b as u128) % d.p as u128) as u64,
            GateOp::Mul => ((a as u128 * b as u128) % d.p as u128) as u64,
        };
        defined[out] = true;
    }
    assert!(
        defined.iter().all(|&x| x),
        "descriptor leaves wires undefined (no gate outputs them)"
    );
    wires
}
