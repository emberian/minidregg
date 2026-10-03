//! Physical public-program BFV transformer. This produces completion candidates,
//! never current-authority tokens, input-validity proofs, or release permission.
use fhe::bfv::{
    BfvParameters, Ciphertext, Encoding, Multiplicator, Plaintext, PublicKey, RelinearizationKey,
};
use fhe_traits::{DeserializeParametrized, DeserializeWithContext, FheEncoder, Serialize};
use prost::Message;
use serde::{Deserialize, Serialize as SerdeSerialize};
use serde_json::Value;
use sha2::{Digest, Sha256};
use std::{collections::BTreeMap, fs, path::Path, sync::Arc};
pub type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;
pub const T: u64 = 1_032_193;
pub const Q: [u64; 3] = [0xffff_ee001, 0xffff_c4001, 0x1_ffff_e0001];
pub const TRANSFORMER: Option<&str> = option_env!("DREGG_FHE_TRANSFORMER_ID");
pub const PROFILE: &str = "bfv-fhe011-degree4096-t1032193-public-literal-enum-depth0-v1";
pub const PRELUDE_PROFILE: &str =
    "bfv-fhe011-degree4096-t1032193-public-prelude-bool-case-depth0-v1";
pub const MUX_PROFILE: &str =
    "bfv-fhe011-degree4096-t1032193-public-core-enum-mux-plan-depth1-lifetime2-v1";
const CAP: usize = 2_000_000;
pub fn ensure(ok: bool, why: &str) -> Result<()> {
    if ok {
        Ok(())
    } else {
        Err(why.into())
    }
}
pub fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}
pub fn unhex(s: &str) -> Result<Vec<u8>> {
    ensure(
        s.len() <= CAP
            && s.len() % 2 == 0
            && s.bytes()
                .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b)),
        "noncanonical hex or capacity",
    )?;
    (0..s.len())
        .step_by(2)
        .map(|i| Ok(u8::from_str_radix(&s[i..i + 2], 16)?))
        .collect()
}
pub fn digest(bytes: &[u8]) -> String {
    hex(&Sha256::digest(bytes))
}
pub fn read(path: &Path) -> Result<Vec<u8>> {
    use std::io::Read;
    let mut bytes = Vec::new();
    fs::File::open(path)?
        .take((CAP + 1) as u64)
        .read_to_end(&mut bytes)?;
    ensure(bytes.len() <= CAP, "file exceeds public capacity")?;
    Ok(bytes)
}
pub fn params() -> Result<Arc<BfvParameters>> {
    let p = BfvParameters::default_parameters_128(20)?
        .nth(2)
        .ok_or("missing pinned parameters")?;
    ensure(
        p.degree() == 4096 && p.plaintext() == T && p.moduli() == Q,
        "parameter drift",
    )?;
    Ok(p)
}
// Public profile excludes symmetric seeded formats and extra-polynomial payloads.
pub fn ciphertext(bytes: &[u8], p: &Arc<BfvParameters>) -> Result<Ciphertext> {
    ensure(bytes.len() <= CAP, "ciphertext capacity")?;
    let proto = fhe::proto::bfv::Ciphertext::decode(bytes)?;
    ensure(
        proto.level == 0 && proto.c.len() == 2 && proto.seed.is_empty(),
        "ciphertext level/degree/seed outside profile",
    )?;
    let ct = Ciphertext::from_bytes(bytes, p)?;
    ensure(
        ct.len() == 2 && p.level_of_context(ct[0].ctx())? == 0 && ct.to_bytes() == bytes,
        "noncanonical ciphertext",
    )?;
    // Decoder alone skips the constructor's NTT/context invariant.
    let checked = Ciphertext::new(ct.iter().cloned().collect(), p)?;
    ensure(
        checked.to_bytes() == bytes,
        "ciphertext representation/context/canonical bytes",
    )?;
    Ok(checked)
}
pub fn public_key(bytes: &[u8], p: &Arc<BfvParameters>) -> Result<PublicKey> {
    ensure(bytes.len() <= CAP, "public key capacity")?;
    let proto = fhe::proto::bfv::PublicKey::decode(bytes)?;
    let inner = proto.c.as_ref().ok_or("public key missing ciphertext")?;
    ensure(
        inner.level == 0
            && ((inner.c.len() == 1 && inner.seed.len() == 32)
                || (inner.c.len() == 2 && inner.seed.is_empty())),
        "public key ciphertext shape",
    )?;
    let ct = Ciphertext::from_bytes(&inner.encode_to_vec(), p)?;
    let _checked = Ciphertext::new(ct.iter().cloned().collect(), p)?;
    let pk = PublicKey::from_bytes(bytes, p)?;
    ensure(pk.to_bytes() == bytes, "noncanonical public key")?;
    Ok(pk)
}
pub fn plain(z: i64, p: &Arc<BfvParameters>) -> Result<Plaintext> {
    ensure((-1..=1).contains(&z), "coefficient outside literal profile")?;
    // Full public capacity, independent of occupied slots. All packed slots
    // belong to the same owner/recipient; packing does not separate audiences.
    Ok(Plaintext::try_encode(
        &vec![z.rem_euclid(T as i64) as u64; 4096],
        Encoding::simd(),
        p,
    )?)
}
/// Exact public material registration manifest; no secret key or proof.
#[derive(Clone, Debug, Deserialize, SerdeSerialize, PartialEq)]
#[serde(deny_unknown_fields)]
pub struct OwnerPublicMaterial {
    pub schema: String,
    pub profile: String,
    pub parameters_sha256: String,
    pub transformer_sha256: String,
    pub public_key: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub relinearization_key: Option<String>,
    pub key_epoch: String,
}
#[derive(Clone, Debug, Deserialize, SerdeSerialize, PartialEq)]
#[serde(deny_unknown_fields)]
pub struct Context {
    pub semantic_id: String,
    pub program_id: String,
    pub method_id: String,
    pub invocation: String,
    pub predecessor: String,
    pub authority_snapshot: String,
    pub tariff_id: String,
    pub canonical_charge: Vec<u64>,
}
#[derive(Clone, Debug, Deserialize, SerdeSerialize, PartialEq)]
#[serde(deny_unknown_fields)]
pub struct Request {
    pub schema: String,
    pub compiler_artifact_sha256: String,
    pub profile: String,
    pub parameters_sha256: String,
    pub transformer_sha256: String,
    pub public_key: String,
    pub key_epoch: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub relinearization_key: Option<String>,
    pub inputs: Vec<String>,
    pub input_depths: Vec<u64>,
    pub context: Context,
    pub input_admission: String,
}
#[derive(Clone, Debug, Deserialize, SerdeSerialize, PartialEq)]
#[serde(deny_unknown_fields)]
pub struct Cost {
    pub ct_add: u64,
    pub ct_plain_add: u64,
    pub ct_plain_mul: u64,
    pub ct_neg: u64,
    pub ct_ct_mul: u64,
    pub relinearizations: u64,
    pub depth: u64,
}
impl Default for Cost {
    fn default() -> Self {
        Self {
            ct_add: 0,
            ct_plain_add: 0,
            ct_plain_mul: 0,
            ct_neg: 0,
            ct_ct_mul: 0,
            relinearizations: 0,
            depth: 0,
        }
    }
}
#[derive(Clone, Debug, Deserialize, SerdeSerialize, PartialEq)]
#[serde(deny_unknown_fields)]
pub struct Completion {
    pub schema: String,
    pub request_sha256: String,
    pub compiler_artifact_sha256: String,
    pub key_epoch: String,
    pub profile: String,
    pub transformer_sha256: String,
    pub parameters_sha256: String,
    pub input_sha256: Vec<String>,
    pub output: String,
    pub output_sha256: String,
    pub physical_cost: Cost,
}
pub fn canonical<TS: serde::Serialize>(value: &TS) -> Result<Vec<u8>> {
    Ok(serde_json::to_vec(value)?)
}
fn field<'a>(v: &'a Value, k: &str) -> Result<&'a Value> {
    v.get(k).ok_or_else(|| format!("missing {k}").into())
}
fn nat(v: &Value, k: &str) -> Result<u64> {
    field(v, k)?
        .as_u64()
        .ok_or_else(|| format!("not natural {k}").into())
}
fn string<'a>(v: &'a Value, k: &str) -> Result<&'a str> {
    field(v, k)?
        .as_str()
        .ok_or_else(|| format!("not string {k}").into())
}
fn signed_to_field(w: &Value) -> Result<Value> {
    if let Some(n) = w.get("w") {
        ensure(w.as_object().map(|o| o.len()) == Some(1), "ambiguous wire")?;
        return Ok(serde_json::json!({"w":n}));
    }
    ensure(
        w.as_object().map(|o| o.len()) == Some(2) && nat(w, "den")? == 1,
        "nonintegral signed constant",
    )?;
    let z = field(w, "z")?.as_i64().ok_or("signed constant")?;
    ensure((-1..=1).contains(&z), "literal constant bound")?;
    Ok(serde_json::json!({"c":z.rem_euclid(2_013_265_921)}))
}
pub fn artifact_arity(a: &Value) -> Result<usize> {
    match string(a, "schema")? {
        "dregg.bend.literal-enum-case.v1" | "dregg.bend.prelude-bool-case.v1" => Ok(1),
        "dregg.bend.dynamic-enum-mux.v1" => Ok(3),
        _ => Err("unsupported source compiler schema".into()),
    }
}
pub fn artifact_profile(a: &Value) -> Result<&'static str> {
    match string(a, "schema")? {
        "dregg.bend.literal-enum-case.v1" => Ok(PROFILE),
        "dregg.bend.prelude-bool-case.v1" => Ok(PRELUDE_PROFILE),
        "dregg.bend.dynamic-enum-mux.v1" => Ok(MUX_PROFILE),
        _ => Err("unsupported source compiler schema".into()),
    }
}
pub fn relinearization_key(bytes: &[u8], p: &Arc<BfvParameters>) -> Result<RelinearizationKey> {
    ensure(bytes.len() <= CAP, "relinearization key capacity")?;
    let proto = fhe::proto::bfv::RelinearizationKey::decode(bytes)?;
    let k = proto
        .ksk
        .as_ref()
        .ok_or("relinearization key missing ksk")?;
    ensure(
        k.ciphertext_level == 0
            && k.ksk_level == 0
            && k.log_base == 0
            && k.c0.len() == 3
            && ((k.seed.len() == 32 && k.c1.is_empty()) || (k.seed.is_empty() && k.c1.len() == 3)),
        "relinearization shape/level",
    )?;
    // Key-switching polynomials use NttShoup, not ciphertext Ntt. The
    // decoder alone does not impose this primitive's representation contract.
    let context = p.context_at_level(0)?;
    for bytes in k.c0.iter().chain(k.c1.iter()) {
        let polynomial = fhe_math::rq::Poly::from_bytes(bytes, context)?;
        ensure(
            polynomial.representation() == &fhe_math::rq::Representation::NttShoup
                && polynomial.to_bytes() == *bytes,
            "relinearization representation/canonical polynomial",
        )?;
    }
    let rk = RelinearizationKey::from_bytes(bytes, p)?;
    ensure(rk.to_bytes() == bytes, "noncanonical relinearization key")?;
    Ok(rk)
}
pub fn validate_artifact(bytes: &[u8], expected: &str) -> Result<Value> {
    ensure(
        digest(bytes) == expected,
        "compiler artifact differs from independently pinned checked bytes",
    )?;
    let a: Value = serde_json::from_slice(bytes)?;
    ensure(
        string(&a, "kernelPin")? == "947db722640c86247849343657bf2f7ef01cb7f1"
            && nat(&a, "compilerVersion")? == 1,
        "unsupported compiler/source",
    )?;
    let arity = artifact_arity(&a)?;
    if string(&a, "schema")? == "dregg.bend.prelude-bool-case.v1" {
        ensure(
            string(&a, "tagEncoding")? == "bend-prelude-bool-sigma-unit-v1"
                && string(&a, "frontendCorrespondence")? == "captured-safe-emit-structure-v1"
                && string(&a, "entry")? == "SourceBool.not"
                && !string(&a, "bookSource")?.is_empty()
                && !string(&a, "surfaceSource")?.is_empty()
                && nat(field(&a, "relation")?, "nPublic")? == 0,
            "Prelude source/representation/profile binding",
        )?;
    }
    ensure(nat(&a, "outputWire")? == 0, "output layout")?;
    if arity == 1 {
        ensure(
            string(&a, "signedConstantPolicy")? == "literal-bool-difference-v1"
                && nat(&a, "inputWire")? == 1,
            "literal codec",
        )?;
        ensure(
            field(&a, "onFalse")?.is_boolean() && field(&a, "onTrue")?.is_boolean(),
            "literal arms",
        )?;
    } else {
        ensure(
            string(&a, "signedConstantPolicy")? == "dynamic-bool-mux-v1"
                && a["inputWires"] == serde_json::json!([1, 2, 3])
                && a["inputOrder"] == serde_json::json!(["selector", "trueArm", "falseArm"]),
            "dynamic mux codec",
        )?;
    }
    let integral = field(&a, "constructiveIntegerOutput")?;
    let modular = field(&a, "constructiveOutput")?;
    ensure(
        nat(integral, "nVars")? == (arity + 1) as u64
            && nat(integral, "nWires")? <= 16
            && integral["nWires"] == modular["nWires"]
            && integral["nVars"] == modular["nVars"],
        "constructive layout",
    )?;
    let gates = field(integral, "gates")?.as_array().ok_or("signed gates")?;
    let mgates = field(modular, "gates")?.as_array().ok_or("modular gates")?;
    ensure(
        gates.len() == mgates.len() && gates.len() + arity + 1 == nat(integral, "nWires")? as usize,
        "gate layout",
    )?;
    for (index, (g, m)) in gates.iter().zip(mgates).enumerate() {
        ensure(
            nat(g, "out")? == index as u64 + arity as u64 + 1
                && g["out"] == m["out"]
                && g["op"] == m["op"],
            "gate provenance",
        )?;
        ensure(
            signed_to_field(field(g, "a")?)? == m["a"]
                && signed_to_field(field(g, "b")?)? == m["b"],
            "signed/field coefficient disagreement",
        )?;
    }
    ensure(
        signed_to_field(field(integral, "output")?)? == modular["output"],
        "output projection disagreement",
    )?;
    ensure(
        nat(field(&a, "relation")?, "p")? == 2_013_265_921,
        "relation carrier changed",
    )?;
    Ok(a)
}
#[derive(Clone)]
enum V {
    Clear(i64),
    Ct(Ciphertext, u64),
}
fn operand(w: &Value, wires: &BTreeMap<u64, V>) -> Result<V> {
    if let Some(i) = w.get("w").and_then(Value::as_u64) {
        return wires
            .get(&i)
            .cloned()
            .ok_or("uncomputed or forbidden wire".into());
    }
    ensure(nat(w, "den")? == 1, "nonintegral operand")?;
    let z = field(w, "z")?.as_i64().ok_or("signed operand")?;
    ensure((-1..=1).contains(&z), "literal operand range")?;
    Ok(V::Clear(z))
}
fn operation(
    op: &str,
    a: V,
    b: V,
    p: &Arc<BfvParameters>,
    cost: &mut Cost,
    rk: Option<&RelinearizationKey>,
    max_depth: u64,
) -> Result<V> {
    let result = match (op, a, b) {
        ("add", V::Clear(a), V::Clear(b)) => V::Clear(a.checked_add(b).ok_or("constant overflow")?),
        ("mul", V::Clear(a), V::Clear(b)) => V::Clear(a.checked_mul(b).ok_or("constant overflow")?),
        ("add", V::Ct(a, da), V::Ct(b, db)) => {
            cost.ct_add += 1;
            V::Ct(&a + &b, da.max(db))
        }
        ("add", V::Ct(a, d), V::Clear(b)) | ("add", V::Clear(b), V::Ct(a, d)) => {
            cost.ct_plain_add += 1;
            V::Ct(&a + &plain(b, p)?, d)
        }
        ("mul", V::Ct(a, d), V::Clear(b)) | ("mul", V::Clear(b), V::Ct(a, d)) => {
            ensure((-1..=1).contains(&b), "signed multiply range")?;
            if b == -1 {
                cost.ct_neg += 1;
                V::Ct(-&a, d)
            } else {
                cost.ct_plain_mul += 1;
                V::Ct(&a * &plain(b, p)?, d)
            }
        }
        ("mul", V::Ct(a, da), V::Ct(b, db)) => {
            let rk = rk.ok_or("depth0 profile refuses ciphertext multiplication")?;
            ensure(cost.ct_ct_mul == 0, "one-product plan budget exceeded")?;
            let depth = da.max(db) + 1;
            ensure(depth <= max_depth, "ciphertext lifetime depth exceeded")?;
            let output = Multiplicator::default(rk)?.multiply(&a, &b)?;
            cost.ct_ct_mul += 1;
            cost.relinearizations += 1;
            V::Ct(output, depth)
        }
        _ => return Err("unsupported constructive gate".into()),
    };
    if let V::Ct(_, depth) = &result {
        cost.depth = cost.depth.max(*depth);
    }
    Ok(result)
}
pub fn evaluate(artifact_bytes: &[u8], expected: &str, request: &Request) -> Result<Completion> {
    let a = validate_artifact(artifact_bytes, expected)?;
    let arity = artifact_arity(&a)?;
    let profile = artifact_profile(&a)?;
    ensure(
        Some(request.transformer_sha256.as_str()) == TRANSFORMER
            && request.transformer_sha256.len() == 64,
        "unqualified physical transformer build",
    )?;
    ensure(
        request.schema == "dregg.fhe-bend.request.v1"
            && request.compiler_artifact_sha256 == expected
            && request.profile == profile,
        "request program/profile",
    )?;
    ensure(
        request.input_admission == "owner-generated-canonical-bool-v1",
        "unsupported input validity contract",
    )?;
    ensure(
        !request.context.invocation.is_empty() && request.context.canonical_charge.len() == 10,
        "incomplete receiving context",
    )?;
    let p = params()?;
    ensure(
        request.parameters_sha256 == digest(&p.to_bytes()),
        "parameters hash",
    )?;
    let pkbytes = unhex(&request.public_key)?;
    let _pk = public_key(&pkbytes, &p)?;
    let rkbytes = match (arity, &request.relinearization_key) {
        (1, None) => Vec::new(),
        (3, Some(bytes)) => unhex(bytes)?,
        _ => return Err("evaluation material outside profile".into()),
    };
    let rk = if arity == 3 {
        Some(relinearization_key(&rkbytes, &p)?)
    } else {
        None
    };
    ensure(
        request.key_epoch == digest(&[p.to_bytes(), pkbytes, rkbytes].concat()),
        "key epoch",
    )?;
    ensure(
        request.inputs.len() == arity && request.input_depths.len() == arity,
        "source input/depth count",
    )?;
    ensure(
        request
            .input_depths
            .iter()
            .all(|d| *d <= if arity == 1 { 0 } else { 1 }),
        "input lifetime depth outside profile",
    )?;
    let inputbytes = request
        .inputs
        .iter()
        .map(|s| unhex(s))
        .collect::<Result<Vec<_>>>()?;
    let mut wires = BTreeMap::new();
    for (index, bytes) in inputbytes.iter().enumerate() {
        wires.insert(
            index as u64 + 1,
            V::Ct(ciphertext(bytes, &p)?, request.input_depths[index]),
        );
    }
    let ct = ciphertext(&inputbytes[0], &p)?;
    let mut cost = Cost::default();
    let expr = field(&a, "constructiveIntegerOutput")?;
    for g in field(expr, "gates")?.as_array().ok_or("gates")? {
        let av = operand(field(g, "a")?, &wires)?;
        let bv = operand(field(g, "b")?, &wires)?;
        let result = operation(
            string(g, "op")?,
            av,
            bv,
            &p,
            &mut cost,
            rk.as_ref(),
            if arity == 1 { 0 } else { 2 },
        )?;
        wires.insert(nat(g, "out")?, result);
    }
    let output = match operand(field(expr, "output")?, &wires)? {
        V::Ct(c, _) => c,
        V::Clear(c) => {
            cost.ct_plain_mul += 1;
            cost.ct_plain_add += 1;
            &(&ct * &plain(0, &p)?) + &plain(c, &p)?
        }
    };
    let bytes = output.to_bytes();
    let _ = ciphertext(&bytes, &p)?;
    Ok(Completion {
        schema: "dregg.fhe-bend.completion-candidate.v1".into(),
        request_sha256: digest(&canonical(request)?),
        compiler_artifact_sha256: expected.into(),
        key_epoch: request.key_epoch.clone(),
        profile: profile.into(),
        transformer_sha256: request.transformer_sha256.clone(),
        parameters_sha256: request.parameters_sha256.clone(),
        input_sha256: inputbytes.iter().map(|b| digest(b)).collect(),
        output: hex(&bytes),
        output_sha256: digest(&bytes),
        physical_cost: cost,
    })
}
pub fn check(
    artifact: &[u8],
    expected: &str,
    request: &Request,
    candidate: &Completion,
) -> Result<()> {
    let replay = evaluate(artifact, expected, request)?;
    ensure(
        &replay == candidate,
        "ciphertext replay or statement binding differs",
    )
}
