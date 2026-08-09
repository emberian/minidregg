//! Data-only reader for the first-order descriptor emitted by Lean.
//!
//! This file only re-declares the transport shape so bytes can be read. It does
//! not validate, interpret, or accept a descriptor. The wire format
//! (`[EMIT-backend]`, concretized in EmitSerialize):
//!
//! ```json
//! { "p": 2013265921, "nPublic": 1, "nVars": 5, "nWires": 23,
//!   "gates": [ {"op": "add", "a": {"w": 1}, "b": {"c": 2013265920}, "out": 5}, ... ],
//!   "zeros": [ {"w": 6}, ... ] }
//! ```
//!
//! Constants and the modulus are transported as integers; Lean-owned generated
//! control establishes every well-formedness and acceptance property.

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

}
