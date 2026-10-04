//! Typed intents over the SHARED-CONTRACTS cuts, their canonical bytes and `InvocationId`.
//!
//! The encoding is DEFINED in Lean: `Kernel/Contracts/Intents.lean` (`intentCodec`, frame
//! `DREGG/CONTRACT/INTENT/v1`, built from the repo's one stream nucleus
//! `Tower256ConcreteBackend.StreamCodec`). This module is the single client-side encoder (the TS
//! SDK reaches it through wasm; there is no third copy) and is held to the Lean codec by
//! `golden/lean-intents.json`, emitted by Lean's own exported entry point
//! (`minidregg_intent_encode`) and compared byte for byte by `tests/golden.rs`.
//!
//! Stream primitives (the Lean names in parentheses):
//! ```text
//! nat(n)      := base-255 little-endian digits of n ‖ 0xFF            (StreamCodec.nat)
//! bytes(b)    := nat(len) ‖ b                                          (bytesStream)
//! string(s)   := nat(#scalars) ‖ nat(scalar)…                          (stringStream)
//! list(f)     := nat(n) ‖ f…                                           (StreamCodec.list)
//! option(f)   := 0 | 1 ‖ f                                             (StreamCodec.option)
//! sum         := nested prefix-free: inl = 0 ‖ x, inr = 1 ‖ y          (StreamCodec.sum)
//! ```
//! Layout:
//! ```text
//! intent      := "DREGG/CONTRACT/INTENT/v1" ‖ bytes(salt[16]) ‖ nat(actor) ‖ cut
//! object      := nat(id) ‖ nat(domain) ‖ string(kind)
//! revision    := object ‖ nat(root)
//! artifact    := bytes(sha256[32]) ‖ nat(length) ‖ string(format)
//! route       := ordinary 0 | objectiveMethod 1 0 | activityDispatch 1 1 0 | roomRelease 1 1 1 0 | roomPublish 1 1 1 1
//! cut         := observe   0              ‖ revision ‖ string(projection) ‖ nat(capability)
//!              | invoke    1 0            ‖ list(revision ‖ nat(cap) ‖ nat(observeCap) ‖ nat(schema) ‖ string(canonical payload JSON))
//!                                          ‖ option(route ‖ bytes(context))
//!              | reserve   1 1 0          ‖ artifact(candidate) ‖ list(object) ‖ artifact(law) ‖ artifact(obligation)
//!              | install   1 1 1 0        ‖ artifact(candidate) ‖ revision(preimage) ‖ artifact(effects) ‖ artifact(obligation)
//!              | release   1 1 1 1 0      ‖ artifact(result) ‖ list(nat audience) ‖ artifact(law)
//!              | retire    1 1 1 1 1      ‖ artifact(obligation) ‖ artifact(evidence)
//! InvocationId := SHA-256("DREGG/CONTRACT/INTENT-ID/v1" ‖ intent)
//! ```
//! This `InvocationId` is the client's stable name for one semantic request, available before
//! the Host assigns the request its (source, transaction, event) coordinate
//! (`Kernel.Contracts.InvocationId`); the salt chosen at creation is what makes it one request.
use serde_json::{json, Map, Value};

use crate::{Error, Result};

/// `intentFrame` in `Kernel/Contracts/Intents.lean`.
pub const INTENT_FRAME: &[u8] = b"DREGG/CONTRACT/INTENT/v1";
/// `intentIdFrame` in `Kernel/Contracts/Intents.lean`.
pub const INTENT_ID_FRAME: &[u8] = b"DREGG/CONTRACT/INTENT-ID/v1";

/// A canonical decimal natural, Mini's spelling of every native identifier and root.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Dec(String);
impl Dec {
    pub fn new(text: &str) -> Result<Self> {
        if !crate::decimal::is_canonical(text) {
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

/// `SHA-256(intentIdFrame ‖ canonical intent)` — see the module docs.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct InvocationId(pub [u8; 32]);
impl InvocationId {
    pub fn hex(&self) -> String {
        crate::hex::encode(&self.0)
    }
}

/// The Lean `StreamCodec` primitives, as byte writers.
struct W(Vec<u8>);
impl W {
    /// `StreamCodec.nat`: base-255 little-endian digits, then 255.
    fn nat_u64(&mut self, mut n: u64) {
        while n > 0 {
            self.0.push((n % 255) as u8);
            n /= 255;
        }
        self.0.push(255);
    }
    fn nat_usize(&mut self, n: usize) {
        self.nat_u64(n as u64);
    }
    /// A canonical decimal natural of any size.
    fn dec(&mut self, d: &Dec) {
        let mut digits: Vec<u8> = d.0.bytes().map(|b| b - b'0').collect();
        // Repeated division by 255 on the decimal digits; remainders are the base-255 digits.
        while digits.iter().any(|&x| x != 0) {
            let mut rem: u32 = 0;
            for x in digits.iter_mut() {
                let cur = rem * 10 + *x as u32;
                *x = (cur / 255) as u8;
                rem = cur % 255;
            }
            self.0.push(rem as u8);
        }
        self.0.push(255);
    }
    fn bytes(&mut self, b: &[u8]) {
        self.nat_usize(b.len());
        self.0.extend_from_slice(b);
    }
    /// `stringStream`: the scalar count, then each scalar value as a `nat`.
    fn str(&mut self, s: &str) {
        self.nat_usize(s.chars().count());
        for c in s.chars() {
            self.nat_u64(c as u64);
        }
    }
    fn list_len(&mut self, n: usize) {
        self.nat_usize(n);
    }
    fn tag(&mut self, bytes: &[u8]) {
        self.0.extend_from_slice(bytes);
    }
    fn object(&mut self, o: &ObjectRef) {
        self.dec(&o.id);
        self.dec(&o.domain);
        self.str(&o.kind);
    }
    fn revision(&mut self, r: &RevisionRef) {
        self.object(&r.object);
        self.dec(&r.root);
    }
    fn artifact(&mut self, a: &ArtifactRef) {
        self.bytes(&a.sha256);
        self.nat_u64(a.length);
        self.str(&a.format);
    }
    /// The nested-sum tag of `routeStream`.
    fn route(&mut self, route: &str) {
        match route {
            "ordinary" => self.tag(&[0]),
            "objectiveMethod" => self.tag(&[1, 0]),
            "activityDispatch" => self.tag(&[1, 1, 0]),
            "roomRelease" => self.tag(&[1, 1, 1, 0]),
            _ => self.tag(&[1, 1, 1, 1]),
        }
    }
}

/// The exact integer a JSON number denotes, if it denotes one of magnitude at most `2^53`: the
/// number's literal read as `digits × 10^exponent`, an integer iff the division is exact. The
/// SPELLING does not matter (`100`, `100.0`, `1e2` are one number), the VALUE does, and a fraction
/// is refused, never rounded (`1.0000000000000000001` is not `1`). This is the twin of Lean's
/// `Kernel.Contracts.Intents.integerValue?` and is held to it by the vectors
/// (`payload-number-*` rows of `golden/intents.json`).
pub fn integer_value(n: &serde_json::Number) -> Option<i64> {
    integer_value_of_literal(&n.to_string())
}

fn integer_value_of_literal(literal: &str) -> Option<i64> {
    let (negative, rest) = match literal.strip_prefix('-') {
        Some(r) => (true, r),
        None => (false, literal),
    };
    let (mantissa, exponent) = match rest.find(['e', 'E']) {
        Some(i) => (&rest[..i], rest[i + 1..].parse::<i64>().ok()?),
        None => (rest, 0),
    };
    let (int, frac) = mantissa.split_once('.').unwrap_or((mantissa, ""));
    if int.is_empty() || !int.bytes().chain(frac.bytes()).all(|b| b.is_ascii_digit()) {
        return None;
    }
    let digits: String = int.chars().chain(frac.chars()).collect();
    let digits = digits.trim_start_matches('0');
    if digits.is_empty() {
        return Some(0);
    }
    // value = digits × 10^-scale
    let scale = i64::try_from(frac.len()).ok()?.checked_sub(exponent)?;
    let whole: String = if scale <= 0 {
        if (digits.len() as i64).checked_add(-scale)? > 16 {
            return None;
        }
        format!("{digits}{}", "0".repeat((-scale) as usize))
    } else {
        let scale = usize::try_from(scale).ok()?;
        if scale > digits.len() || digits[digits.len() - scale..].bytes().any(|b| b != b'0') {
            return None;
        }
        digits[..digits.len() - scale].to_owned()
    };
    let magnitude: i64 = whole.parse().ok()?;
    if magnitude > 1 << 53 {
        return None;
    }
    Some(if negative { -magnitude } else { magnitude })
}

/// Canonical JSON: object keys sorted by UTF-8 bytes, no whitespace, strings escaped as
/// `serde_json` escapes them, numbers only integers of magnitude <= 2^53 (written as plain
/// integers, see [`integer_value`]). Anything else is refused. This is the twin of Lean's
/// `Kernel.Contracts.Intents.canonText`.
pub fn canonical_json(value: &Value) -> Result<String> {
    fn write(v: &Value, out: &mut String) -> Result<()> {
        match v {
            Value::Null => out.push_str("null"),
            Value::Bool(b) => out.push_str(if *b { "true" } else { "false" }),
            Value::Number(n) => match integer_value(n) {
                Some(i) => out.push_str(&i.to_string()),
                None => return Err("canonical JSON admits only integers of magnitude ≤ 2^53; use a decimal string".into()),
            },
            Value::String(s) => out.push_str(&serde_json::to_string(s).map_err(|e| Error(e.to_string()))?),
            Value::Array(a) => {
                out.push('[');
                for (i, x) in a.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    write(x, out)?;
                }
                out.push(']');
            }
            Value::Object(o) => {
                // serde_json's Map (no `preserve_order`) is a BTreeMap: keys iterate in byte order.
                out.push('{');
                for (i, (k, x)) in o.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    out.push_str(&serde_json::to_string(k).map_err(|e| Error(e.to_string()))?);
                    out.push(':');
                    write(x, out)?;
                }
                out.push('}');
            }
        }
        Ok(())
    }
    let mut out = String::new();
    write(value, &mut out)?;
    Ok(out)
}

impl Intent {
    /// The Lean codec's bytes (`intentCodec.encode`), or the named refusal.
    pub fn canonical_bytes(&self) -> Result<Vec<u8>> {
        let mut w = W(INTENT_FRAME.to_vec());
        w.bytes(&self.request_salt);
        w.dec(&self.actor);
        match &self.cut {
            Cut::Observe { resource, projection, capability } => {
                w.tag(&[0]);
                w.revision(resource);
                w.str(projection);
                w.dec(capability);
            }
            Cut::Invoke { targets, family } => {
                if targets.is_empty() {
                    return Err("an invocation names at least one target".into());
                }
                w.tag(&[1, 0]);
                w.list_len(targets.len());
                for t in targets {
                    w.revision(&t.revision);
                    w.dec(&t.capability);
                    w.dec(&t.observe_capability);
                    w.dec(&t.schema_version);
                    w.str(&canonical_json(&t.payload)?);
                }
                match family {
                    None => w.tag(&[0]),
                    Some(f) => {
                        if !ROUTES.contains(&f.route.as_str()) {
                            return Err(Error(format!("unknown invocation family route {:?}", f.route)));
                        }
                        w.tag(&[1]);
                        w.route(&f.route);
                        w.bytes(&f.context);
                    }
                }
            }
            Cut::Reserve { candidate, footprint, law, obligation } => {
                w.tag(&[1, 1, 0]);
                w.artifact(candidate);
                w.list_len(footprint.len());
                for o in footprint {
                    w.object(o);
                }
                w.artifact(law);
                w.artifact(obligation);
            }
            Cut::Install { candidate, preimage, effects, obligation } => {
                w.tag(&[1, 1, 1, 0]);
                w.artifact(candidate);
                w.revision(preimage);
                w.artifact(effects);
                w.artifact(obligation);
            }
            Cut::Release { result, audience, law } => {
                w.tag(&[1, 1, 1, 1, 0]);
                w.artifact(result);
                w.list_len(audience.len());
                for d in audience {
                    w.dec(d);
                }
                w.artifact(law);
            }
            Cut::Retire { obligation, evidence } => {
                w.tag(&[1, 1, 1, 1, 1]);
                w.artifact(obligation);
                w.artifact(evidence);
            }
        }
        Ok(w.0)
    }

    /// The bytes hashed into the `InvocationId` (`intentIdPreimage` in Lean).
    pub fn id_preimage(&self) -> Result<Vec<u8>> {
        let mut pre = INTENT_ID_FRAME.to_vec();
        pre.extend(self.canonical_bytes()?);
        Ok(pre)
    }

    pub fn invocation_id(&self) -> Result<InvocationId> {
        Ok(InvocationId(crate::sha256(&self.id_preimage()?)))
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
        let length = o["length"].as_number().and_then(integer_value).and_then(|n| u64::try_from(n).ok())
            .ok_or("length must be a natural number ≤ 2^53")?;
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
    fn the_integer_rule_is_by_value_exact_and_bounded() {
        // The cases of Lean's `integerValue_cases` theorem, spelled as JSON literals.
        let n = |lit: &str| serde_json::from_str::<serde_json::Number>(lit).ok().and_then(|n| integer_value(&n));
        for (lit, want) in [("100", Some(100)), ("100.0", Some(100)), ("1e2", Some(100)), ("1E2", Some(100)), ("15e-1", None),
            ("1.5", None), ("-50", Some(-50)), ("-5.0e1", Some(-50)), ("0.0", Some(0)), ("-0", Some(0)), ("0e7", Some(0)),
            ("1e-400000", None), ("1e-2", None), ("1.0000000000000000001", None),
            ("9007199254740992", Some(9007199254740992)), ("9007199254740993", None), ("1e400", None),
            ("900719925474099200e-2", Some(9007199254740992)), ("-9007199254740992", Some(-9007199254740992))] {
            assert_eq!(n(lit), want, "{lit}");
        }
        assert_eq!(canonical_json(&serde_json::from_str("{\"b\":1e1,\"a\":[2.0,-0]}").unwrap()).unwrap(), "{\"a\":[2,0],\"b\":10}");
        assert!(canonical_json(&serde_json::from_str("[1.5]").unwrap()).is_err());
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
