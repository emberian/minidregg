//! Bounded natural add-only source contract. All envelopes are CONDITIONAL:
//! source inputs obey caps and each fresh ciphertext has phase L(m)+E with
//! |E|<=FRESH_NOISE. Syntax/public replay cannot establish either premise.
//! The abstract lift/rounding and actual NTT/RNS implementation refinement
//! remain separate proof obligations. No inherited ciphertext freshness reset.
use crate::*;
pub const SCHEMA: &str = "dregg.bend.public-natural-expression.v1";
pub const PROFILE: &str = "bfv-fhe011-degree4096-t1032193-public-natural-add-fresh-depth0-v1";
pub const FRESH_NOISE: u128 = 3_276_820;
const MAX_INPUTS: usize = 16;
const MAX_GATES: usize = 64;
#[derive(Clone, Debug, Deserialize, SerdeSerialize, PartialEq)]
#[serde(deny_unknown_fields)]
pub struct ConditionalEnvelope {
    pub model: String,
    pub premise: String,
    pub input_caps: Vec<u64>,
    pub output_max: u64,
    pub coefficient_noise_bound: String,
    pub strict_rounding_margin: bool,
}
#[derive(Clone, Copy)]
struct Bound { max: u64, noise: u128, encrypted: bool }
#[derive(Clone)]
enum Value { Clear(u64), Ct(Ciphertext) }
fn add_bound(a: Bound, b: Bound) -> Result<Bound> {
    let max = a.max.checked_add(b.max).ok_or("natural interval overflow")?;
    ensure(max < T, "natural intermediate wraps plaintext modulus")?;
    let encrypted = a.encrypted || b.encrypted;
    let noise = a.noise.checked_add(b.noise)
        .and_then(|v| v.checked_add(u128::from(encrypted)))
        .ok_or("conditional noise overflow")?;
    Ok(Bound { max, noise, encrypted })
}
fn constant(w: &ValueJson) -> Result<u64> {
    ensure(w.as_object().map(|o| o.len()) == Some(2) && nat(w,"den")? == 1,
        "natural signed integral constant shape")?;
    let z = field(w,"z")?.as_u64().ok_or("natural constant negative/nonintegral")?;
    ensure(z < T, "natural constant outside plaintext modulus")?;
    Ok(z)
}
type ValueJson = serde_json::Value;
fn bound_operand(w: &ValueJson, wires: &BTreeMap<u64, Bound>) -> Result<Bound> {
    if let Some(i) = w.get("w").and_then(ValueJson::as_u64) {
        ensure(w.as_object().map(|o| o.len()) == Some(1), "ambiguous natural wire")?;
        return wires.get(&i).copied().ok_or("uncomputed natural wire".into());
    }
    Ok(Bound { max:constant(w)?, noise:0, encrypted:false })
}
fn value_operand(w: &ValueJson, wires: &BTreeMap<u64, Value>) -> Result<Value> {
    if let Some(i) = w.get("w").and_then(ValueJson::as_u64) {
        return wires.get(&i).cloned().ok_or("uncomputed natural value".into());
    }
    Ok(Value::Clear(constant(w)?))
}
pub fn caps(a: &ValueJson) -> Result<Vec<u64>> {
    let values = field(a,"inputCaps")?.as_array().ok_or("input caps")?;
    ensure(!values.is_empty() && values.len() <= MAX_INPUTS, "natural input capacity")?;
    values.iter().map(|v| {
        let cap = v.as_u64().ok_or("non-natural input cap")?;
        ensure(cap > 0 && cap <= T, "input cap outside natural profile")?;
        Ok(cap)
    }).collect()
}
// Independent source-expression oracle, never uses the constructive DAG.
// Inclusive maximum uses cap-1 for each admitted input.
fn expression(e: &ValueJson, inputs: &[u64], fuel: &mut usize) -> Result<u64> {
    ensure(*fuel > 0, "natural expression exceeds public node capacity")?;
    *fuel -= 1;
    ensure(e.as_object().map(|o| o.len()) == Some(1), "natural expression shape")?;
    if let Some(i) = e.get("input").and_then(ValueJson::as_u64) {
        return inputs.get(usize::try_from(i)?).copied().ok_or("expression input index".into());
    }
    if let Some(z) = e.get("literal").and_then(ValueJson::as_u64) {
        ensure(z < T, "expression literal modulus")?;
        return Ok(z);
    }
    let add = e.get("add").and_then(ValueJson::as_array).ok_or("unsupported source expression")?;
    ensure(add.len() == 2, "source addition arity")?;
    let l = expression(&add[0], inputs, fuel)?;
    let r = expression(&add[1], inputs, fuel)?;
    let result = l.checked_add(r).ok_or("source natural overflow")?;
    ensure(result < T, "source natural addition wraps")?;
    Ok(result)
}
pub fn source_value(a: &ValueJson, inputs: &[u64]) -> Result<u64> {
    let bounds = caps(a)?;
    ensure(inputs.len() == bounds.len()
        && inputs.iter().zip(&bounds).all(|(x,cap)| x < cap), "owner source input outside admitted cap")?;
    expression(field(a,"expression")?, inputs, &mut (2*MAX_GATES+1))
}
pub fn validate(a: &ValueJson) -> Result<ConditionalEnvelope> {
    ensure(string(a,"signedConstantPolicy")? == "bounded-natural-polynomial-v1"
        && string(a,"tagEncoding")? == "bend-prelude-nat-scalar-v1"
        && string(a,"frontendCorrespondence")? == "captured-safe-emit-structure-v1"
        && !string(a,"bookSource")?.is_empty() && !string(a,"surfaceSource")?.is_empty()
        && !string(a,"entry")?.is_empty()
        && string(a,"sourceChargePolicy")? == "bend-live-eval-natural-expression-v1"
        && nat(a,"chargeReservation")? > 0, "natural checked source/representation/charge binding")?;
    let caps = caps(a)?;
    let arity = caps.len();
    ensure(a["inputWires"] == serde_json::json!((1..=arity).collect::<Vec<_>>())
        && nat(a,"outputWire")? == 0
        && nat(field(a,"relation")?,"nPublic")? == 0
        && nat(field(a,"relation")?,"p")? == 2_013_265_921, "natural interface/relation")?;
    let max_inputs: Vec<u64> = caps.iter().map(|c|c-1).collect();
    let source_max = expression(field(a,"expression")?, &max_inputs, &mut (2*MAX_GATES+1))?;
    ensure(nat(a,"outputMax")? == source_max, "source interval declaration differs")?;
    let graph = field(a,"constructiveIntegerOutput")?;
    let modular = field(a,"constructiveOutput")?;
    let gates = field(graph,"gates")?.as_array().ok_or("natural gates")?;
    let mgates = field(modular,"gates")?.as_array().ok_or("natural modular gates")?;
    ensure(gates.len() <= MAX_GATES && gates.len() == mgates.len()
        && nat(graph,"nVars")? == (arity+1) as u64
        && nat(graph,"nWires")? == (arity+1+gates.len()) as u64
        && graph["nVars"] == modular["nVars"] && graph["nWires"] == modular["nWires"],
        "natural constructive layout")?;
    let mut wires = BTreeMap::new();
    for (i,cap) in caps.iter().enumerate() {
        wires.insert(i as u64+1, Bound{max:cap-1,noise:FRESH_NOISE,encrypted:true});
    }
    for (i,(g,m)) in gates.iter().zip(mgates).enumerate() {
        ensure(string(g,"op")? == "add" && g["op"] == m["op"]
            && nat(g,"out")? == (arity+1+i) as u64 && g["out"] == m["out"],
            "natural profile permits ordered addition only")?;
        for name in ["a","b"] {
            let signed = field(g,name)?;
            let projection = if let Some(w) = signed.get("w") {
                serde_json::json!({"w":w})
            } else { serde_json::json!({"c":constant(signed)?}) };
            ensure(projection == m[name], "natural signed/field projection")?;
        }
        let b = add_bound(bound_operand(field(g,"a")?, &wires)?,
                          bound_operand(field(g,"b")?, &wires)?)?;
        wires.insert(nat(g,"out")?, b);
    }
    let output = field(graph,"output")?;
    let projection = if let Some(w) = output.get("w") {
        serde_json::json!({"w":w})
    } else { serde_json::json!({"c":constant(output)?}) };
    ensure(projection == modular["output"], "natural output projection")?;
    let mut b = bound_operand(output, &wires)?;
    ensure(b.max == source_max, "constructive/source range disagreement")?;
    // Public constant output uses nonempty ct*0+constant, with conditional
    // zero-message phase and one rounding defect. No empty zero serialization.
    if !b.encrypted { b.noise = 1; }
    let q = Q.iter().map(|x|*x as u128).product::<u128>();
    let lhs = b.noise.checked_add(1).and_then(|v|v.checked_mul(2*T as u128))
        .ok_or("rounding margin overflow")?;
    ensure(lhs < q, "conditional linear noise exhausts strict rounding margin")?;
    Ok(ConditionalEnvelope{
        model:"floor-qm-over-t-coefficient-linear-v1".into(),
        premise:"honest-owner-fresh-cbd-variance10-phase-and-bounded-natural-inputs; actual-ntt-rns-rounding-correspondence-required".into(),
        input_caps:caps, output_max:source_max,
        coefficient_noise_bound:b.noise.to_string(), strict_rounding_margin:true,
    })
}
fn plain_nat(z:u64,p:&Arc<BfvParameters>) -> Result<Plaintext> {
    ensure(z<T,"natural plaintext constant wrap")?;
    Ok(Plaintext::try_encode(&vec![z;4096],Encoding::simd(),p)?)
}
pub fn evaluate(a:&ValueJson, expected:&str, request:&Request) -> Result<Completion> {
    let envelope=validate(a)?;
    ensure(Some(request.transformer_sha256.as_str())==TRANSFORMER
        && request.transformer_sha256.len()==64, "unqualified natural transformer")?;
    ensure(request.schema=="dregg.fhe-bend.request.v1"
        && request.compiler_artifact_sha256==expected && request.profile==PROFILE
        && request.input_admission=="honest-owner-fresh-bounded-natural-v1"
        && request.relinearization_key.is_none(), "natural source/phase/input profile")?;
    ensure(!request.context.invocation.is_empty() && request.context.canonical_charge.len()==10,
        "natural receiving context")?;
    let p=params()?;
    ensure(request.parameters_sha256==digest(&p.to_bytes()),"natural parameter hash")?;
    let pkbytes=unhex(&request.public_key)?;
    let _pk=public_key(&pkbytes,&p)?;
    ensure(request.key_epoch==digest(&[p.to_bytes(),pkbytes].concat()),"natural key epoch")?;
    let arity=envelope.input_caps.len();
    ensure(request.inputs.len()==arity && request.input_depths.len()==arity
        && request.input_depths.iter().all(|d|*d==0), "fresh-only natural lineage")?;
    let inputbytes=request.inputs.iter().map(|s|unhex(s)).collect::<Result<Vec<_>>>()?;
    let mut wires=BTreeMap::new();
    for (i,bytes) in inputbytes.iter().enumerate() {
        wires.insert(i as u64+1,Value::Ct(ciphertext(bytes,&p)?));
    }
    let graph=field(a,"constructiveIntegerOutput")?;
    let mut cost=Cost::default();
    for g in field(graph,"gates")?.as_array().ok_or("natural gates")? {
        let left=value_operand(field(g,"a")?,&wires)?;
        let right=value_operand(field(g,"b")?,&wires)?;
        let result=match(left,right) {
            (Value::Clear(x),Value::Clear(y))=>Value::Clear(x.checked_add(y).ok_or("natural constant overflow")?),
            (Value::Ct(x),Value::Ct(y))=>{cost.ct_add+=1;Value::Ct(&x+&y)},
            (Value::Ct(x),Value::Clear(y))|(Value::Clear(y),Value::Ct(x))=>{
                cost.ct_plain_add+=1;Value::Ct(&x+&plain_nat(y,&p)?)
            }
        };
        wires.insert(nat(g,"out")?,result);
    }
    let ct=match value_operand(field(graph,"output")?,&wires)? {
        Value::Ct(ct)=>ct,
        Value::Clear(z)=>{
            cost.ct_plain_mul+=1;cost.ct_plain_add+=1;
            let input=ciphertext(&inputbytes[0],&p)?;
            &(&input*&plain_nat(0,&p)?)+&plain_nat(z,&p)?
        }
    };
    let bytes=ct.to_bytes();
    let _checked=ciphertext(&bytes,&p)?;
    Ok(Completion{
        schema:"dregg.fhe-bend.completion-candidate.v1".into(),
        request_sha256:digest(&canonical(request)?),
        compiler_artifact_sha256:expected.into(),key_epoch:request.key_epoch.clone(),
        profile:PROFILE.into(),transformer_sha256:request.transformer_sha256.clone(),
        parameters_sha256:request.parameters_sha256.clone(),
        input_sha256:inputbytes.iter().map(|b|digest(b)).collect(),
        output:hex(&bytes),output_sha256:digest(&bytes),physical_cost:cost,
        conditional_linear_envelope:Some(envelope),
    })
}
