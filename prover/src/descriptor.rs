//! The Rust mirror of `Compiler/Emit.lean`'s `ConstraintDescriptor`, plus the serde
//! reader for the JSON that `Compiler/EmitSerialize.lean` writes.
//!
//! Mirror, not source of truth: the Lean structure is authoritative; this file only
//! re-declares its shape so the bytes can be read. The wire format
//! (`[EMIT-backend]`, concretized in EmitSerialize):
//!
//! ```json
//! { "p": 2013265921, "nPublic": 1, "nVars": 5, "nWires": 23,
//!   "gates": [ {"op": "add", "a": {"w": 1}, "b": {"c": 2013265920}, "out": 5}, ... ],
//!   "zeros": [ {"w": 6}, ... ] }
//! ```
//!
//! Constants travel as canonical naturals (`ZMod.val`, `0 <= v < p`); the modulus is
//! stamped in the header. `validate` mirrors `ConstraintDescriptor.WellFormed`
//! (Emit §6) plus constant canonicity — a reader-side input contract, not a proof.

use std::path::Path;

use serde::Deserialize;

/// A field element in canonical form: `0 <= x < p`. The modulus travels in the
/// descriptor header (`Descriptor::p`); BabyBear `p = 2^31 - 2^27 + 1 = 2013265921`
/// is the deployed instantiation (`[PROVER-field]`).
pub type Fp = u64;

/// Mirror of `Minidregg.Compiler.GateOp`: the two gate operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum GateOp {
    Add,
    Mul,
}

impl GateOp {
    /// Mirror of `GateOp.denote` at `ZMod p`: field add/mul on canonical
    /// representatives (u128 intermediates, exact for any u64 modulus).
    pub fn denote(self, a: Fp, b: Fp, p: u64) -> Fp {
        match self {
            GateOp::Add => ((a as u128 + b as u128) % p as u128) as u64,
            GateOp::Mul => ((a as u128 * b as u128) % p as u128) as u64,
        }
    }
}

/// Mirror of `DWire`: a literal field constant (`{"c": v}`, canonical) or an index
/// into the one total wire vector (`{"w": n}`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
pub enum Wire {
    #[serde(rename = "c")]
    Const(u64),
    #[serde(rename = "w")]
    Wire(u32),
}

/// Mirror of `DGate`: `a op b = out`, inputs by constant-or-index, output by index.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Gate {
    pub op: GateOp,
    pub a: Wire,
    pub b: Wire,
    pub out: u32,
}

/// Mirror of `ConstraintDescriptor`, plus the field modulus the Lean writer stamps.
/// Layout convention (Emit §1): wires `[0, nPublic)` are the public inputs,
/// `[0, nVars)` the original variables, `[nVars, nWires)` the flattener's aux wires.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct Descriptor {
    pub p: u64,
    pub n_public: u32,
    pub n_vars: u32,
    pub n_wires: u32,
    pub gates: Vec<Gate>,
    pub zeros: Vec<Wire>,
}

impl Descriptor {
    /// Parse a descriptor from JSON text.
    pub fn from_json_str(s: &str) -> Result<Descriptor, String> {
        serde_json::from_str(s).map_err(|e| format!("descriptor parse error: {e}"))
    }

    /// Read and parse a descriptor file.
    pub fn from_file(path: &Path) -> Result<Descriptor, String> {
        let s = std::fs::read_to_string(path)
            .map_err(|e| format!("cannot read {}: {e}", path.display()))?;
        Self::from_json_str(&s)
    }

    /// Reader-side input contract, mirroring `ConstraintDescriptor.WellFormed`
    /// (Emit §6: nested split, all operands bounded by `nWires`, gate outputs in
    /// the aux region `[nVars, nWires)`) plus constant canonicity (`v < p`).
    /// The Lean side PROVED the emitted descriptor satisfies this
    /// (`emit_wellFormed`); here it is re-checked on the parsed bytes.
    pub fn validate(&self) -> Result<(), String> {
        if self.p < 2 {
            return Err(format!("modulus {} is not a field modulus", self.p));
        }
        if !(self.n_public <= self.n_vars && self.n_vars <= self.n_wires) {
            return Err(format!(
                "split not nested: nPublic={} nVars={} nWires={}",
                self.n_public, self.n_vars, self.n_wires
            ));
        }
        let check_wire = |what: &str, w: &Wire| -> Result<(), String> {
            match *w {
                Wire::Const(c) if c >= self.p => Err(format!(
                    "{what}: non-canonical constant {c} (mod {})",
                    self.p
                )),
                Wire::Wire(n) if n >= self.n_wires => Err(format!(
                    "{what}: wire index {n} out of range (nWires={})",
                    self.n_wires
                )),
                _ => Ok(()),
            }
        };
        for (i, g) in self.gates.iter().enumerate() {
            check_wire(&format!("gate {i} input a"), &g.a)?;
            check_wire(&format!("gate {i} input b"), &g.b)?;
            if !(self.n_vars <= g.out && g.out < self.n_wires) {
                return Err(format!(
                    "gate {i}: output {} outside aux region [{}, {})",
                    g.out, self.n_vars, self.n_wires
                ));
            }
        }
        for (i, z) in self.zeros.iter().enumerate() {
            check_wire(&format!("zero-check {i}"), z)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn wire_json_forms() {
        assert_eq!(Wire::Const(5), serde_json::from_str(r#"{"c": 5}"#).unwrap());
        assert_eq!(Wire::Wire(3), serde_json::from_str(r#"{"w": 3}"#).unwrap());
        assert_eq!(GateOp::Add, serde_json::from_str(r#""add""#).unwrap());
        assert_eq!(GateOp::Mul, serde_json::from_str(r#""mul""#).unwrap());
    }

    #[test]
    fn validate_rejects_output_outside_aux_region() {
        let d = Descriptor {
            p: 7,
            n_public: 1,
            n_vars: 1,
            n_wires: 2,
            gates: vec![Gate {
                op: GateOp::Mul,
                a: Wire::Wire(0),
                b: Wire::Wire(0),
                out: 0,
            }],
            zeros: vec![],
        };
        assert!(d.validate().is_err());
    }

    #[test]
    fn validate_rejects_non_canonical_constant() {
        let d = Descriptor {
            p: 7,
            n_public: 0,
            n_vars: 0,
            n_wires: 1,
            gates: vec![Gate {
                op: GateOp::Add,
                a: Wire::Const(7),
                b: Wire::Const(0),
                out: 0,
            }],
            zeros: vec![],
        };
        assert!(d.validate().is_err());
    }
}
