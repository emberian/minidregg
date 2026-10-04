//! Typed intents over the SHARED-CONTRACTS cuts, their canonical bytes and `InvocationId`.
//!
//! TODO(W2.A): lane W2.A owns these types in Lean (`Kernel/Contracts/*`). When that codec
//! lands, replace [`Intent::canonical_bytes`] with golden vectors emitted by the Lean codec and
//! delete this encoder: one encoder, Lean-authored. Until then the encoding below is SDK-owned,
//! domain-tagged `MINI/SDK/INTENT/v1`, and pinned by `golden/vectors.json` in both the Rust
//! and TS suites.
//!
//! Canonical encoding (all integers little-endian):
//! ```text
//! intent      := "MINI/SDK/INTENT/v1" ‖ salt[16] ‖ dec(actor) ‖ u8(cut tag) ‖ body
//! str(s)      := u32(len) ‖ utf8          dec(s) := str(s), s a canonical decimal
//! bytes(b)    := u32(len) ‖ b             list(f) := u32(n) ‖ f…    opt(f) := 0 | 1 ‖ f
//! objectRef   := dec(id) ‖ dec(domain) ‖ str(kind)
//! revisionRef := objectRef ‖ dec(root)
//! artifactRef := sha256[32] ‖ u64(length) ‖ str(format)
//! json(v)     := str(canonical JSON: sorted keys, no whitespace, integers only)
//! 1 Observe   := revisionRef ‖ str(projection) ‖ dec(capability)
//! 2 Invoke    := list(revisionRef ‖ dec(cap) ‖ dec(observeCap) ‖ dec(schemaVersion) ‖ json(payload))
//!                ‖ opt(str(route) ‖ bytes(context))
//! 3 Reserve   := artifactRef(candidate) ‖ list(objectRef) ‖ artifactRef(law) ‖ artifactRef(obligation)
//! 4 Install   := artifactRef(candidate) ‖ revisionRef(preimage) ‖ artifactRef(effects) ‖ artifactRef(obligation)
//! 5 Release   := artifactRef(result) ‖ list(dec audience) ‖ artifactRef(law)
//! 6 Retire    := artifactRef(obligation) ‖ artifactRef(evidence)
//! InvocationId := SHA-256("MINI/SDK/INVOCATION-ID/v1" ‖ intent)
//! ```
use serde_json::{json, Map, Value};

use crate::hex::is_decimal;
use crate::{Error, Result};

pub const INTENT_DOMAIN: &[u8] = b"MINI/SDK/INTENT/v1";
pub const INVOCATION_DOMAIN: &[u8] = b"MINI/SDK/INVOCATION-ID/v1";

/// A canonical decimal natural, Mini's spelling of every native identifier and root.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Dec(String);
impl Dec {
    pub fn new(text: &str) -> Result<Self> {
        if !is_decimal(text) {
            return Err(Error(format!("{text:?} is not a canonical decimal")));
        }
        Ok(Dec(text.to_owned()))
    }
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

/// Native identity + governing domain + declared semantic kind.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ObjectRef {
    pub id: Dec,
    pub domain: Dec,
    pub kind: String,
}
/// An exact root of an object: never latest-by-name.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RevisionRef {
    pub object: ObjectRef,
    pub root: Dec,
}
/// Exact bytes: digest, length, format. A content address confers no permission.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ArtifactRef {
    pub sha256: [u8; 32],
    pub length: u64,
    pub format: String,
}

/// The native invocation routes the signed command may carry (`workspace.rs`
/// `invocation_family`).
pub const ROUTES: &[&str] = &["ordinary", "objectiveMethod", "activityDispatch", "roomRelease", "roomPublish"];

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Family {
    pub route: String,
    pub context: Vec<u8>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InvokeTarget {
    pub revision: RevisionRef,
    pub capability: Dec,
    pub observe_capability: Dec,
    pub schema_version: Dec,
    /// The target payload exactly as the native author reads it (`content`, `scalar`,
    /// `append`, `world`, `kindDefinition`, `computeFunding`, `read`).
    pub payload: Value,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Cut {
    Observe { resource: RevisionRef, projection: String, capability: Dec },
    Invoke { targets: Vec<InvokeTarget>, family: Option<Family> },
    Reserve { candidate: ArtifactRef, footprint: Vec<ObjectRef>, law: ArtifactRef, obligation: ArtifactRef },
    Install { candidate: ArtifactRef, preimage: RevisionRef, effects: ArtifactRef, obligation: ArtifactRef },
    Release { result: ArtifactRef, audience: Vec<Dec>, law: ArtifactRef },
    Retire { obligation: ArtifactRef, evidence: ArtifactRef },
}

impl Cut {
    pub fn tag(&self) -> u8 {
        match self {
            Cut::Observe { .. } => 1,
            Cut::Invoke { .. } => 2,
            Cut::Reserve { .. } => 3,
            Cut::Install { .. } => 4,
            Cut::Release { .. } => 5,
            Cut::Retire { .. } => 6,
        }
    }
    pub fn name(&self) -> &'static str {
        ["observe", "invoke", "reserve", "install", "release", "retire"][self.tag() as usize - 1]
    }
}

/// One semantic request by one actor. The salt is chosen once, at creation, so two deliberate
/// identical requests are two invocations and a retry of one is never a second.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Intent {
    pub actor: Dec,
    pub request_salt: [u8; 16],
    pub cut: Cut,
}

/// `SHA-256("MINI/SDK/INVOCATION-ID/v1" ‖ canonical intent)`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct InvocationId(pub [u8; 32]);
impl InvocationId {
    pub fn hex(&self) -> String {
        crate::hex::encode(&self.0)
    }
}

struct W(Vec<u8>);
impl W {
    fn u32(&mut self, n: usize) -> Result<()> {
        let n: u32 = n.try_into().map_err(|_| "intent field exceeds u32 length")?;
        self.0.extend_from_slice(&n.to_le_bytes());
        Ok(())
    }
    fn bytes(&mut self, b: &[u8]) -> Result<()> {
        self.u32(b.len())?;
        self.0.extend_from_slice(b);
        Ok(())
    }
    fn str(&mut self, s: &str) -> Result<()> {
        self.bytes(s.as_bytes())
    }
    fn dec(&mut self, d: &Dec) -> Result<()> {
        self.str(&d.0)
    }
    fn object(&mut self, o: &ObjectRef) -> Result<()> {
        self.dec(&o.id)?;
        self.dec(&o.domain)?;
        self.str(&o.kind)
    }
    fn revision(&mut self, r: &RevisionRef) -> Result<()> {
        self.object(&r.object)?;
        self.dec(&r.root)
    }
    fn artifact(&mut self, a: &ArtifactRef) -> Result<()> {
        self.0.extend_from_slice(&a.sha256);
        self.0.extend_from_slice(&a.length.to_le_bytes());
        self.str(&a.format)
    }
}

/// Canonical JSON: object keys sorted by UTF-8 bytes, no whitespace, strings escaped as
/// `serde_json` escapes them, numbers restricted to integers of magnitude ≤ 2^53 so every
/// implementation (including JavaScript) reads them identically. Floats are refused.
pub fn canonical_json(value: &Value) -> Result<String> {
    fn check(v: &Value) -> Result<()> {
        match v {
            Value::Number(n) => {
                let ok = n.as_i64().is_some_and(|i| i.unsigned_abs() <= 1 << 53)
                    || n.as_u64().is_some_and(|u| u <= 1 << 53);
                if ok { Ok(()) } else { Err("canonical JSON admits only integers of magnitude ≤ 2^53; use a decimal string".into()) }
            }
            Value::Array(a) => a.iter().try_for_each(check),
            Value::Object(o) => o.values().try_for_each(check),
            _ => Ok(()),
        }
    }
    check(value)?;
    // serde_json's Map (no `preserve_order`) is a BTreeMap: keys are emitted in byte order.
    serde_json::to_string(value).map_err(|e| Error(e.to_string()))
}

impl Intent {
    pub fn canonical_bytes(&self) -> Result<Vec<u8>> {
        let mut w = W(INTENT_DOMAIN.to_vec());
        w.0.extend_from_slice(&self.request_salt);
        w.dec(&self.actor)?;
        w.0.push(self.cut.tag());
        match &self.cut {
            Cut::Observe { resource, projection, capability } => {
                w.revision(resource)?;
                w.str(projection)?;
                w.dec(capability)?;
            }
            Cut::Invoke { targets, family } => {
                if targets.is_empty() {
                    return Err("an invocation names at least one target".into());
                }
                w.u32(targets.len())?;
                for t in targets {
                    w.revision(&t.revision)?;
                    w.dec(&t.capability)?;
                    w.dec(&t.observe_capability)?;
                    w.dec(&t.schema_version)?;
                    w.str(&canonical_json(&t.payload)?)?;
                }
                match family {
                    None => w.0.push(0),
                    Some(f) => {
                        if !ROUTES.contains(&f.route.as_str()) {
                            return Err(Error(format!("unknown invocation family route {:?}", f.route)));
                        }
                        w.0.push(1);
                        w.str(&f.route)?;
                        w.bytes(&f.context)?;
                    }
                }
            }
            Cut::Reserve { candidate, footprint, law, obligation } => {
                w.artifact(candidate)?;
                w.u32(footprint.len())?;
                for o in footprint {
                    w.object(o)?;
                }
                w.artifact(law)?;
                w.artifact(obligation)?;
            }
            Cut::Install { candidate, preimage, effects, obligation } => {
                w.artifact(candidate)?;
                w.revision(preimage)?;
                w.artifact(effects)?;
                w.artifact(obligation)?;
            }
            Cut::Release { result, audience, law } => {
                w.artifact(result)?;
                w.u32(audience.len())?;
                for d in audience {
                    w.dec(d)?;
                }
                w.artifact(law)?;
            }
            Cut::Retire { obligation, evidence } => {
                w.artifact(obligation)?;
                w.artifact(evidence)?;
            }
        }
        Ok(w.0)
    }

    pub fn invocation_id(&self) -> Result<InvocationId> {
        let mut pre = INVOCATION_DOMAIN.to_vec();
        pre.extend(self.canonical_bytes()?);
        Ok(InvocationId(crate::sha256(&pre)))
    }

    /// Lower to the authoring JSON the local Host's `author intent` (op 7) reads, for the
    /// attempt whose fresh nonces are given. Only `Invoke` has a common native wire today;
    /// every other cut refuses with a named reason rather than guessing one.
    pub fn lower(&self, ctx: &Lowering) -> Result<Value> {
        let Cut::Invoke { targets, family } = &self.cut else {
            return Err(Error(format!(
                "{} has no common native wire yet (SHARED-CONTRACTS cut without a source counterpart); not lowered",
                self.cut.name()
            )));
        };
        let mut grants = Vec::new();
        let mut wire = Vec::new();
        for t in targets {
            let o = &t.revision.object;
            if o.domain != ctx.domain {
                return Err(Error(format!("target {} is governed by domain {}, not this deployment's {}",
                    o.id.as_str(), o.domain.as_str(), ctx.domain.as_str())));
            }
            grants.push(json!({"capability":t.observe_capability.as_str(),"kind":o.kind,"target":o.id.as_str()}));
            wire.push(json!({"capability":t.capability.as_str(),"expectedTargetRoot":t.revision.root.as_str(),
                "kind":o.kind,"observeCapability":t.observe_capability.as_str(),"payload":t.payload,
                "schemaVersion":t.schema_version.as_str(),"target":o.id.as_str()}));
        }
        let mut command = Map::new();
        command.insert("nonce".into(), json!(ctx.command_nonce.as_str()));
        command.insert("subject".into(), json!(self.actor.as_str()));
        command.insert("targets".into(), Value::Array(wire));
        if let Some(f) = family {
            command.insert("family".into(), json!({"route":f.route,"contextBytes":crate::hex::encode(&f.context)}));
        }
        Ok(json!({"grants":grants,"nonce":ctx.intent_nonce.as_str(),
            "purpose":{"draft":{"command":Value::Object(command),"type":"invoke"},"type":"prepare"},
            "subject":self.actor.as_str()}))
    }
}

/// The JSON spelling of an intent (the TS SDK's object shape; also what the wasm oracle reads):
/// `{"actor", "salt": hex16, "cut": "observe"|…, …fields}` with `ObjectRef` as
/// `{"id","domain","kind"}`, `RevisionRef` as `{"object", "root"}`, `ArtifactRef` as
/// `{"sha256": hex32, "length": n, "format"}`. Unknown or missing fields refuse.
pub mod spelling {
    use super::*;

    fn exact<'a>(v: &'a Value, keys: &[&str]) -> Result<&'a Map<String, Value>> {
        let o = v.as_object().ok_or("expected an object")?;
        if o.len() != keys.len() || keys.iter().any(|k| !o.contains_key(*k)) {
            return Err(Error(format!("expected exactly the fields {keys:?}")));
        }
        Ok(o)
    }
    fn s(v: &Value) -> Result<String> {
        v.as_str().map(str::to_owned).ok_or_else(|| "expected a string".into())
    }
    fn d(v: &Value) -> Result<Dec> {
        Dec::new(v.as_str().ok_or("expected a decimal string")?)
    }
    fn object(v: &Value) -> Result<ObjectRef> {
        let o = exact(v, &["id", "domain", "kind"])?;
        Ok(ObjectRef { id: d(&o["id"])?, domain: d(&o["domain"])?, kind: s(&o["kind"])? })
    }
    fn revision(v: &Value) -> Result<RevisionRef> {
        let o = exact(v, &["object", "root"])?;
        Ok(RevisionRef { object: object(&o["object"])?, root: d(&o["root"])? })
    }
    fn artifact(v: &Value) -> Result<ArtifactRef> {
        let o = exact(v, &["sha256", "length", "format"])?;
        let sha: [u8; 32] = crate::hex::decode(&s(&o["sha256"])?)?.try_into().map_err(|_| "sha256 must be 32 bytes")?;
        let length = o["length"].as_u64().filter(|n| *n <= 1 << 53).ok_or("length must be an integer ≤ 2^53")?;
        Ok(ArtifactRef { sha256: sha, length, format: s(&o["format"])? })
    }
    fn list<T>(v: &Value, f: impl Fn(&Value) -> Result<T>) -> Result<Vec<T>> {
        v.as_array().ok_or("expected a list")?.iter().map(f).collect()
    }

    pub fn intent(v: &Value) -> Result<Intent> {
        let cut = v.get("cut").and_then(Value::as_str).ok_or("intent has no cut")?;
        let fields: &[&str] = match cut {
            "observe" => &["actor", "salt", "cut", "resource", "projection", "capability"],
            "invoke" => &["actor", "salt", "cut", "targets", "family"],
            "reserve" => &["actor", "salt", "cut", "candidate", "footprint", "law", "obligation"],
            "install" => &["actor", "salt", "cut", "candidate", "preimage", "effects", "obligation"],
            "release" => &["actor", "salt", "cut", "result", "audience", "law"],
            "retire" => &["actor", "salt", "cut", "obligation", "evidence"],
            _ => return Err(Error(format!("unknown cut {cut:?}"))),
        };
        let o = exact(v, fields)?;
        let salt: [u8; 16] = crate::hex::decode(&s(&o["salt"])?)?.try_into().map_err(|_| "salt must be 16 bytes")?;
        let cut = match cut {
            "observe" => Cut::Observe { resource: revision(&o["resource"])?, projection: s(&o["projection"])?, capability: d(&o["capability"])? },
            "invoke" => Cut::Invoke {
                targets: list(&o["targets"], |t| {
                    let t = exact(t, &["revision", "capability", "observeCapability", "schemaVersion", "payload"])?;
                    Ok(InvokeTarget { revision: revision(&t["revision"])?, capability: d(&t["capability"])?,
                        observe_capability: d(&t["observeCapability"])?, schema_version: d(&t["schemaVersion"])?,
                        payload: t["payload"].clone() })
                })?,
                family: match &o["family"] {
                    Value::Null => None,
                    f => {
                        let f = exact(f, &["route", "context"])?;
                        Some(Family { route: s(&f["route"])?, context: crate::hex::decode(&s(&f["context"])?)? })
                    }
                },
            },
            "reserve" => Cut::Reserve { candidate: artifact(&o["candidate"])?, footprint: list(&o["footprint"], object)?,
                law: artifact(&o["law"])?, obligation: artifact(&o["obligation"])? },
            "install" => Cut::Install { candidate: artifact(&o["candidate"])?, preimage: revision(&o["preimage"])?,
                effects: artifact(&o["effects"])?, obligation: artifact(&o["obligation"])? },
            "release" => Cut::Release { result: artifact(&o["result"])?, audience: list(&o["audience"], d)?, law: artifact(&o["law"])? },
            _ => Cut::Retire { obligation: artifact(&o["obligation"])?, evidence: artifact(&o["evidence"])? },
        };
        Ok(Intent { actor: d(&o["actor"])?, request_salt: salt, cut })
    }

    pub fn lowering(v: &Value) -> Result<Lowering> {
        let o = exact(v, &["domain", "intentNonce", "commandNonce"])?;
        Ok(Lowering { domain: d(&o["domain"])?, intent_nonce: d(&o["intentNonce"])?, command_nonce: d(&o["commandNonce"])? })
    }
}

/// Per-attempt lowering context. Both nonces are fresh per attempt; the InvocationId is not.
#[derive(Debug, Clone)]
pub struct Lowering {
    pub domain: Dec,
    pub intent_nonce: Dec,
    pub command_nonce: Dec,
}

#[cfg(test)]
mod tests {
    use super::*;

    pub(crate) fn object(id: &str) -> ObjectRef {
        ObjectRef { id: Dec::new(id).unwrap(), domain: Dec::new("8501").unwrap(), kind: "object".into() }
    }

    #[test]
    fn salt_distinguishes_identical_requests_and_actor_is_bound() {
        let cut = Cut::Retire {
            obligation: ArtifactRef { sha256: [1; 32], length: 3, format: "x".into() },
            evidence: ArtifactRef { sha256: [2; 32], length: 4, format: "y".into() },
        };
        let a = Intent { actor: Dec::new("7").unwrap(), request_salt: [0; 16], cut: cut.clone() };
        let mut b = a.clone();
        b.request_salt[0] = 1;
        let mut c = a.clone();
        c.actor = Dec::new("8").unwrap();
        let ids = [a.invocation_id().unwrap(), b.invocation_id().unwrap(), c.invocation_id().unwrap()];
        assert!(ids[0] != ids[1] && ids[0] != ids[2] && ids[1] != ids[2]);
        assert_eq!(a.invocation_id().unwrap(), a.clone().invocation_id().unwrap());
    }

    #[test]
    fn noncanonical_decimals_unknown_routes_floats_and_empty_invokes_refuse() {
        assert!(Dec::new("007").is_err());
        let target = InvokeTarget {
            revision: RevisionRef { object: object("1"), root: Dec::new("2").unwrap() },
            capability: Dec::new("3").unwrap(),
            observe_capability: Dec::new("3").unwrap(),
            schema_version: Dec::new("9").unwrap(),
            payload: json!({"type":"read"}),
        };
        let mut i = Intent { actor: Dec::new("5").unwrap(), request_salt: [0; 16],
            cut: Cut::Invoke { targets: vec![target.clone()], family: Some(Family { route: "bogus".into(), context: vec![] }) } };
        assert!(i.canonical_bytes().is_err());
        i.cut = Cut::Invoke { targets: vec![], family: None };
        assert!(i.canonical_bytes().is_err());
        let mut t = target;
        t.payload = json!({"x": 1.5});
        i.cut = Cut::Invoke { targets: vec![t], family: None };
        assert!(i.canonical_bytes().is_err());
    }

    #[test]
    fn non_invoke_cuts_refuse_to_lower_and_foreign_domains_refuse() {
        let ctx = Lowering { domain: Dec::new("8501").unwrap(), intent_nonce: Dec::new("1").unwrap(), command_nonce: Dec::new("2").unwrap() };
        let i = Intent { actor: Dec::new("5").unwrap(), request_salt: [0; 16], cut: Cut::Release {
            result: ArtifactRef { sha256: [0; 32], length: 0, format: "f".into() }, audience: vec![],
            law: ArtifactRef { sha256: [0; 32], length: 0, format: "f".into() } } };
        assert!(i.lower(&ctx).unwrap_err().0.contains("release has no common native wire"));
        let mut o = object("1");
        o.domain = Dec::new("9").unwrap();
        let i = Intent { actor: Dec::new("5").unwrap(), request_salt: [0; 16], cut: Cut::Invoke { targets: vec![InvokeTarget {
            revision: RevisionRef { object: o, root: Dec::new("2").unwrap() }, capability: Dec::new("3").unwrap(),
            observe_capability: Dec::new("3").unwrap(), schema_version: Dec::new("9").unwrap(), payload: json!({"type":"read"}) }], family: None } };
        assert!(i.lower(&ctx).unwrap_err().0.contains("governed by domain 9"));
    }
}
