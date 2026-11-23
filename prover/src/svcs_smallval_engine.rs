//! Oracle-mode SVCS zerocheck. Two chained repetitions use the same normalized witness.
//! The prover delays extension-field promotion for the first two variables. The verifier
//! replays the cubic sumcheck, reads terminal MLEs from the witness, and checks projective
//! LogUp fraction trees. The verifier requires a trusted statement and the full witness.

pub use crate::sensory_roi_cert::{Ext4, W_EXT4 as W};
use crate::{babybear, hash_kernels::cshake256_xof};
use sha3::{Digest, Sha3_256};

pub const P: u32 = babybear::P as u32;
pub type BabyBearExt4 = Ext4;
/// Canonical base-field element in `[0, P)`.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct Fp(pub u32);

impl Fp {
    pub const ZERO: Fp = Fp(0);
    pub const ONE: Fp = Fp(1);
    #[inline]
    pub fn new(x: u64) -> Fp {
        Fp((x % P as u64) as u32)
    }
    #[inline]
    pub fn from_i128(x: i128) -> Fp {
        Fp(x.rem_euclid(P as i128) as u32)
    }
    #[inline]
    pub fn add(self, o: Fp) -> Fp {
        Fp(babybear::badd(self.0.into(), o.0.into()) as u32)
    }
    #[inline]
    pub fn sub(self, o: Fp) -> Fp {
        Fp(babybear::bsub(self.0.into(), o.0.into()) as u32)
    }
    #[inline]
    pub fn mul(self, o: Fp) -> Fp {
        Fp(babybear::bmul(self.0.into(), o.0.into()) as u32)
    }
    pub fn inv(self) -> Fp {
        Fp(babybear::binv(self.0.into()) as u32)
    }
    /// Signed representative in `(-P/2, P/2]`.
    #[inline]
    pub fn signed(self) -> i64 {
        if self.0 > P / 2 {
            self.0 as i64 - P as i64
        } else {
            self.0 as i64
        }
    }
}

trait LiftBase {
    fn from_base(x: Fp) -> Self;
    fn mul_base(self, b: Fp) -> Self;
}
impl LiftBase for Ext4 {
    #[inline]
    fn from_base(x: Fp) -> Self {
        Self::from_bb(x.0)
    }
    #[inline]
    fn mul_base(self, b: Fp) -> Self {
        self.scale_bb(b.0)
    }
}

#[inline]
fn eq1(a: Ext4, x: Ext4) -> Ext4 {
    // a·x + (1 - a)(1 - x)
    a.mul(x).add(Ext4::ONE.sub(a).mul(Ext4::ONE.sub(x)))
}

/// `eq(τ, k)` for all `k < 2^{|τ|}`, bit `i` of `k` paired with `τ_i` (LSB first).
pub fn eq_table(tau: &[Ext4]) -> Vec<Ext4> {
    let mut t = vec![Ext4::ONE];
    for &ti in tau {
        let one_m = Ext4::ONE.sub(ti);
        let n = t.len();
        let mut nt = vec![Ext4::ZERO; 2 * n];
        for k in 0..n {
            nt[k] = t[k].mul(one_m);
            nt[k + n] = t[k].mul(ti);
        }
        t = nt;
    }
    t
}

/// Evaluate the degree-≤3 polynomial with values `e[0..4]` at `0,1,2,3` at `x`.
pub fn interp4(e: &[Ext4; 4], x: Ext4) -> Ext4 {
    let c = |n: u32| Ext4::from_base(Fp(n));
    let inv2 = Fp(2).inv();
    let inv6 = Fp(6).inv();
    let (x1, x2, x3) = (x.sub(c(1)), x.sub(c(2)), x.sub(c(3)));
    let l0 = Ext4::ZERO.sub(x1.mul(x2).mul(x3).mul_base(inv6));
    let l1 = x.mul(x2).mul(x3).mul_base(inv2);
    let l2 = Ext4::ZERO.sub(x.mul(x1).mul(x3).mul_base(inv2));
    let l3 = x.mul(x1).mul(x2).mul_base(inv6);
    e[0].mul(l0)
        .add(e[1].mul(l1))
        .add(e[2].mul(l2))
        .add(e[3].mul(l3))
}

// ─────────────────────────────── §2. Minimal JSON ───────────────────────────────

/// A JSON value (the crate has no non-dev serde dependency, so the engine parses its own input).
#[derive(Clone, Debug, PartialEq)]
enum Json {
    Null,
    Bool(bool),
    Num(i128),
    Str(String),
    Arr(Vec<Json>),
    Obj(Vec<(String, Json)>),
}

impl Json {
    pub fn get(&self, k: &str) -> Option<&Json> {
        match self {
            Json::Obj(kv) => kv.iter().find(|(kk, _)| kk == k).map(|(_, v)| v),
            _ => None,
        }
    }
    pub fn arr(&self) -> Result<&[Json], String> {
        match self {
            Json::Arr(a) => Ok(a),
            _ => Err("expected array".into()),
        }
    }
    pub fn num(&self) -> Result<i128, String> {
        match self {
            Json::Num(n) => Ok(*n),
            _ => Err("expected number".into()),
        }
    }
    pub fn str(&self) -> Result<&str, String> {
        match self {
            Json::Str(s) => Ok(s),
            _ => Err("expected string".into()),
        }
    }
}

fn parse_json(s: &str) -> Result<Json, String> {
    let b = s.as_bytes();
    let mut i = 0usize;
    let v = parse_value(b, &mut i, 0)?;
    skip_ws(b, &mut i);
    if i != b.len() {
        return Err(format!("trailing data at {i}"));
    }
    Ok(v)
}

fn skip_ws(b: &[u8], i: &mut usize) {
    while *i < b.len() && (b[*i] as char).is_ascii_whitespace() {
        *i += 1;
    }
}

fn hex_quad(b: &[u8], i: &mut usize) -> Result<u16, String> {
    let mut word = 0;
    for _ in 0..4 {
        let digit = b
            .get(*i)
            .and_then(|&c| (c as char).to_digit(16))
            .ok_or("invalid Unicode escape")?;
        word = (word << 4) | digit as u16;
        *i += 1;
    }
    Ok(word)
}

fn json_string(b: &[u8], i: &mut usize) -> Result<Json, String> {
    let mut bytes = Vec::new();
    *i += 1;
    while let Some(&byte) = b.get(*i) {
        *i += 1;
        match byte {
            b'"' => {
                return String::from_utf8(bytes)
                    .map(Json::Str)
                    .map_err(|e| e.to_string())
            }
            0..=31 => return Err("unescaped control character".into()),
            b'\\' => {
                let escape = *b.get(*i).ok_or("unfinished escape")?;
                *i += 1;
                match escape {
                    b'"' | b'\\' | b'/' => bytes.push(escape),
                    b'b' => bytes.push(8),
                    b'f' => bytes.push(12),
                    b'n' => bytes.push(10),
                    b'r' => bytes.push(13),
                    b't' => bytes.push(9),
                    b'u' => {
                        let hi = hex_quad(b, i)?;
                        let code = if (0xd800..=0xdbff).contains(&hi) {
                            if !b[*i..].starts_with(br"\u") {
                                return Err("missing low surrogate".into());
                            }
                            *i += 2;
                            let lo = hex_quad(b, i)?;
                            if !(0xdc00..=0xdfff).contains(&lo) {
                                return Err("invalid low surrogate".into());
                            }
                            0x10000 + (u32::from(hi - 0xd800) << 10) + u32::from(lo - 0xdc00)
                        } else {
                            u32::from(hi)
                        };
                        let c = char::from_u32(code).ok_or("invalid Unicode scalar")?;
                        bytes.extend_from_slice(c.encode_utf8(&mut [0; 4]).as_bytes());
                    }
                    _ => return Err("unknown string escape".into()),
                }
            }
            _ => bytes.push(byte),
        }
    }
    Err("unterminated string".into())
}

fn parse_value(b: &[u8], i: &mut usize, depth: usize) -> Result<Json, String> {
    if depth > 64 {
        return Err("nesting too deep".into());
    }
    skip_ws(b, i);
    if *i >= b.len() {
        return Err("unexpected end".into());
    }
    match b[*i] {
        b'{' => {
            *i += 1;
            let mut kv = Vec::new();
            skip_ws(b, i);
            if *i < b.len() && b[*i] == b'}' {
                *i += 1;
                return Ok(Json::Obj(kv));
            }
            loop {
                let k = match parse_value(b, i, depth + 1)? {
                    Json::Str(s) => s,
                    _ => return Err("object key must be string".into()),
                };
                skip_ws(b, i);
                if *i >= b.len() || b[*i] != b':' {
                    return Err("expected ':'".into());
                }
                *i += 1;
                if kv.iter().any(|(key, _)| key == &k) {
                    return Err("duplicate JSON key".into());
                }
                kv.push((k, parse_value(b, i, depth + 1)?));
                skip_ws(b, i);
                match b.get(*i) {
                    Some(b',') => *i += 1,
                    Some(b'}') => {
                        *i += 1;
                        return Ok(Json::Obj(kv));
                    }
                    _ => return Err("expected ',' or '}'".into()),
                }
            }
        }
        b'[' => {
            *i += 1;
            let mut a = Vec::new();
            skip_ws(b, i);
            if *i < b.len() && b[*i] == b']' {
                *i += 1;
                return Ok(Json::Arr(a));
            }
            loop {
                a.push(parse_value(b, i, depth + 1)?);
                skip_ws(b, i);
                match b.get(*i) {
                    Some(b',') => *i += 1,
                    Some(b']') => {
                        *i += 1;
                        return Ok(Json::Arr(a));
                    }
                    _ => return Err("expected ',' or ']'".into()),
                }
            }
        }
        b'"' => json_string(b, i),
        b't' if b[*i..].starts_with(b"true") => {
            *i += 4;
            Ok(Json::Bool(true))
        }
        b'f' if b[*i..].starts_with(b"false") => {
            *i += 5;
            Ok(Json::Bool(false))
        }
        b'n' if b[*i..].starts_with(b"null") => {
            *i += 4;
            Ok(Json::Null)
        }
        c if c == b'-' || c.is_ascii_digit() => {
            let neg = c == b'-';
            if neg {
                *i += 1;
            }
            if b.get(*i) == Some(&b'0') && b.get(*i + 1).is_some_and(u8::is_ascii_digit) {
                return Err("leading zero".into());
            }
            let st = *i;
            let mut n: i128 = 0;
            while *i < b.len() && b[*i].is_ascii_digit() {
                n = n
                    .checked_mul(10)
                    .and_then(|n| n.checked_add((b[*i] - b'0') as i128))
                    .ok_or("number overflow")?;
                *i += 1;
            }
            if *i == st {
                return Err("bad number".into());
            }
            if *i < b.len() && matches!(b[*i], b'.' | b'e' | b'E') {
                return Err("non-integer numbers unsupported".into());
            }
            Ok(Json::Num(if neg { -n } else { n }))
        }
        c => Err(format!("unexpected byte {c} at {i}")),
    }
}

// ─────────────────────────────── §3. SVCS bundles ───────────────────────────────

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Lane {
    U8,
    I8,
    I16,
    U32,
}

impl Lane {
    /// The Lean `LaneSemantics BB` reading of a canonical value.
    pub fn admits(self, v: u32) -> bool {
        if v >= P {
            return false;
        }
        match self {
            Lane::U8 => v < 256,
            Lane::I8 => v < 128 || v >= P - 128,
            Lane::I16 => v < 32768 || v >= P - 32768,
            Lane::U32 => true,
        }
    }
}

/// `(coefficient, wire)`.
pub type LinForm = Vec<(Fp, usize)>;

#[derive(Clone, Debug, PartialEq)]
pub struct Row {
    pub prods: Vec<(LinForm, LinForm)>,
    pub c: LinForm,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Lookup {
    pub f: Vec<usize>,
    pub table: Vec<Fp>,
}

/// The public statement.
#[derive(Clone, Debug, PartialEq)]
pub struct SvcsInstance {
    pub n_z: usize,
    pub rows: Vec<Row>,
    pub lookups: Vec<Lookup>,
}

/// A Lean-emitted bundle: statement + prover hints (lane tags) + witness.
#[derive(Clone, Debug)]
pub struct SvcsBundle {
    pub name: String,
    extractor: Vec<BackStep>,
    oracle_len: usize,
    pub extracted: Vec<u32>,
    pub instance: SvcsInstance,
    pub tags: Vec<(usize, Lane)>,
    pub witness: Vec<u32>,
    pub lean_check: bool,
    pub cost_before: u64,
    pub cost_after: u64,
    pub rows_before: u64,
    pub n_z_before: u64,
}

/// Backward maps in forward trace order. Unused coordinates of the finite oracle are zero.
#[derive(Clone, Debug)]
enum BackStep {
    Scatter { old_len: usize, keep: Vec<usize> },
    Recover { wire: usize, form: LinForm },
}

impl SvcsBundle {
    pub fn from_json(input: &str) -> Result<Self, String> {
        parse_bundle(&parse_json(input)?)
    }

    // The verifier selects the Lean-emitted statement and extraction map. Bind both
    // so even equivalent optimized rows cannot be replayed with another readback.
    fn bundle_context(&self, session: &[u8]) -> [u8; 32] {
        let mut h = Sha3_256::new();
        h.update(b"svcs/v2/compiled-readback");
        for bytes in [session, self.name.as_bytes()] {
            h.update((bytes.len() as u64).to_le_bytes());
            h.update(bytes);
        }
        h.update(self.n_z_before.to_le_bytes());
        h.update((self.extractor.len() as u64).to_le_bytes());
        for step in &self.extractor {
            match step {
                BackStep::Scatter { old_len, keep } => {
                    h.update(b"D");
                    h.update((*old_len as u64).to_le_bytes());
                    h.update((keep.len() as u64).to_le_bytes());
                    for &i in keep {
                        h.update((i as u64).to_le_bytes());
                    }
                }
                BackStep::Recover { wire, form } => {
                    h.update(b"F");
                    h.update((*wire as u64).to_le_bytes());
                    h.update((form.len() as u64).to_le_bytes());
                    for &(c, i) in form {
                        h.update(c.0.to_le_bytes());
                        h.update((i as u64).to_le_bytes());
                    }
                }
            }
        }
        h.finalize().into()
    }

    pub fn prove(
        &self,
        z: &[u32],
        mode: ProverMode,
        session: &[u8],
    ) -> Result<(SvcsProof, ProverStats), String> {
        SvcsProver::prove_in_context(
            &self.instance,
            z,
            &self.tags,
            mode,
            &self.bundle_context(session),
        )
    }

    pub fn verify_and_extract(
        &self,
        z: &[u32],
        proof: &SvcsProof,
        session: &[u8],
    ) -> Result<Vec<u32>, String> {
        SvcsVerifier::verify_in_context(&self.instance, z, proof, &self.bundle_context(session))?;
        self.extract_witness(z)
    }

    /// Replay the compiler-supplied map from a trusted bundle.
    pub fn extract_witness(&self, oracle: &[u32]) -> Result<Vec<u32>, String> {
        self.instance.validate(oracle)?;
        if oracle.len() != self.oracle_len {
            return Err("extractor oracle shape".into());
        }
        let mut z = oracle.to_vec();
        for step in self.extractor.iter().rev() {
            match step {
                BackStep::Recover { wire, form } => {
                    z[*wire] = lin(&z, form).0;
                }
                BackStep::Scatter { old_len, keep } => {
                    let mut old = vec![0; *old_len];
                    for (&i, v) in keep.iter().zip(z) {
                        old[i] = v;
                    }
                    z = old;
                }
            }
        }
        Ok(z[1..].to_vec())
    }
}

fn parse_fp(j: &Json) -> Result<Fp, String> {
    let n = j.num()?;
    if !(0..P as i128).contains(&n) {
        return Err(format!("non-canonical field element {n}"));
    }
    Ok(Fp(n as u32))
}

fn parse_wire(j: &Json, n_z: usize) -> Result<usize, String> {
    let w = j.num()?;
    if w < 0 || w >= n_z as i128 {
        return Err(format!("wire {w} out of range"));
    }
    Ok(w as usize)
}

fn parse_form(j: &Json, n_z: usize) -> Result<LinForm, String> {
    j.arr()?
        .iter()
        .map(|t| {
            let t = t.arr()?;
            if t.len() != 2 {
                return Err("term must be [coeff, wire]".into());
            }
            Ok((parse_fp(&t[0])?, parse_wire(&t[1], n_z)?))
        })
        .collect()
}

fn parse_u64(j: &Json) -> Result<u64, String> {
    let n = j.num()?;
    u64::try_from(n).map_err(|_| format!("expected non-negative integer, got {n}"))
}

fn parse_bundle(j: &Json) -> Result<SvcsBundle, String> {
    let g = |k: &str| j.get(k).ok_or(format!("missing {k}"));
    let n_z = usize::try_from(parse_u64(g("n_z")?)?).map_err(|e| e.to_string())?;
    let rows = g("rows")?
        .arr()?
        .iter()
        .map(|r| {
            let prods = r
                .get("p")
                .ok_or("missing p")?
                .arr()?
                .iter()
                .map(|ab| {
                    let ab = ab.arr()?;
                    if ab.len() != 2 {
                        return Err("product must be [a, b]".to_string());
                    }
                    Ok((parse_form(&ab[0], n_z)?, parse_form(&ab[1], n_z)?))
                })
                .collect::<Result<Vec<_>, String>>()?;
            Ok(Row {
                prods,
                c: parse_form(r.get("c").ok_or("missing c")?, n_z)?,
            })
        })
        .collect::<Result<Vec<_>, String>>()?;
    let lookups = g("lookups")?
        .arr()?
        .iter()
        .map(|l| {
            let f = l
                .get("f")
                .ok_or("missing f")?
                .arr()?
                .iter()
                .map(|x| parse_wire(x, n_z))
                .collect::<Result<Vec<_>, String>>()?;
            let table = l
                .get("table")
                .ok_or("missing table")?
                .arr()?
                .iter()
                .map(parse_fp)
                .collect::<Result<Vec<_>, String>>()?;
            Ok(Lookup { f, table })
        })
        .collect::<Result<Vec<_>, String>>()?;
    let tags = g("tags")?
        .arr()?
        .iter()
        .map(|t| {
            let t = t.arr()?;
            if t.len() != 2 {
                return Err("tag must be a wire-lane pair".into());
            }
            let lane = match t.get(1).ok_or("bad tag")?.str()? {
                "u8" => Lane::U8,
                "i8" => Lane::I8,
                "i16" => Lane::I16,
                "u32" => Lane::U32,
                o => return Err(format!("unknown lane {o}")),
            };
            Ok((parse_wire(&t[0], n_z)?, lane))
        })
        .collect::<Result<Vec<_>, String>>()?;
    let witness = g("witness")?
        .arr()?
        .iter()
        .map(|x| parse_fp(x).map(|f| f.0))
        .collect::<Result<Vec<_>, String>>()?;
    if witness.len() != n_z {
        return Err("witness length != n_z".into());
    }
    let extracted = g("extracted")?
        .arr()?
        .iter()
        .map(|x| parse_fp(x).map(|v| v.0))
        .collect::<Result<Vec<_>, _>>()?;
    let mut len = extracted.len() + 1;
    if parse_u64(g("n_z_before")?)? != len as u64 {
        return Err("front witness shape".into());
    }
    let mut extractor = Vec::new();
    for entry in g("extractor")?.arr()? {
        if entry == &Json::Null {
            continue;
        }
        if let Some(v) = entry.get("keep") {
            let keep = v
                .arr()?
                .iter()
                .map(|x| parse_wire(x, len))
                .collect::<Result<Vec<_>, _>>()?;
            if keep.first() != Some(&0)
                || keep.iter().collect::<std::collections::HashSet<_>>().len() != keep.len()
            {
                return Err("invalid extraction renumbering".into());
            }
            let old_len = len;
            len = keep.len();
            extractor.push(BackStep::Scatter { old_len, keep });
        } else {
            let wire = parse_wire(entry.get("wire").ok_or("missing pivot")?, len)?;
            let form = parse_form(entry.get("form").ok_or("missing form")?, len)?;
            if wire == 0 || form.iter().any(|p| p.1 == wire) {
                return Err("invalid pivot form".into());
            }
            extractor.push(BackStep::Recover { wire, form });
        }
    }
    if len != n_z {
        return Err("extraction shape".into());
    }
    Ok(SvcsBundle {
        oracle_len: n_z,
        extractor,
        extracted,
        name: g("name")?.str()?.to_string(),
        instance: SvcsInstance { n_z, rows, lookups },
        tags,
        witness,
        lean_check: matches!(j.get("lean_check"), Some(Json::Bool(true))),
        cost_before: parse_u64(g("cost_before")?)?,
        cost_after: parse_u64(g("cost_after")?)?,
        rows_before: parse_u64(g("rows_before")?)?,
        n_z_before: parse_u64(g("n_z_before")?)?,
    })
}

/// Parse a whole conformance file; checks field parameters and the Lean self-check block.
pub fn parse_conformance(s: &str) -> Result<Vec<SvcsBundle>, String> {
    let j = parse_json(s)?;
    if j.get("schema").and_then(|s| s.str().ok()) != Some("minidregg.svcs_compiler_conformance.v1")
    {
        return Err("unknown SVCS schema".into());
    }
    let f = j.get("field").ok_or("missing field")?;
    if f.get("p").map(|x| x.num()) != Some(Ok(P as i128))
        || f.get("w").map(|x| x.num()) != Some(Ok(W as i128))
        || f.get("ext_degree").map(|x| x.num()) != Some(Ok(4))
    {
        return Err("field parameters mismatch".into());
    }
    match j.get("lean_self_checks") {
        Some(Json::Obj(kv)) if !kv.is_empty() => {
            if let Some((k, _)) = kv.iter().find(|(_, v)| *v != Json::Bool(true)) {
                return Err(format!("Lean self-check {k} is not true"));
            }
        }
        _ => return Err("missing lean_self_checks".into()),
    }
    j.get("bundles")
        .ok_or("missing bundles")?
        .arr()?
        .iter()
        .map(parse_bundle)
        .collect()
}

fn lin(z: &[u32], f: &LinForm) -> Fp {
    f.iter()
        .fold(Fp::ZERO, |acc, &(c, w)| acc.add(c.mul(Fp(z[w]))))
}

impl SvcsInstance {
    fn validate(&self, z: &[u32]) -> Result<(), String> {
        if self.n_z != z.len() || z.first() != Some(&1) || z.iter().any(|&x| x >= P) {
            return Err("invalid normalized witness".into());
        }
        let valid = |f: &LinForm| f.iter().all(|&(c, i)| c.0 < P && i < z.len());
        if self
            .rows
            .iter()
            .any(|r| !valid(&r.c) || r.prods.iter().any(|(a, b)| !valid(a) || !valid(b)))
        {
            return Err("malformed row".into());
        }
        if self.lookups.iter().any(|l| {
            l.f.len() >= P as usize
                || l.f.iter().any(|&i| i >= z.len())
                || l.table.iter().any(|v| v.0 >= P)
        }) {
            return Err("lookup wire, table value or query count out of bounds".into());
        }
        Ok(())
    }

    /// Direct (non-protocol) satisfaction check — the Lean `SvcsInstance.Satisfied`.
    pub fn satisfied(&self, z: &[u32]) -> bool {
        self.validate(z).is_ok()
            && self.rows.iter().all(|r| {
                r.prods.iter().fold(lin(z, &r.c), |acc, (a, b)| {
                    acc.add(lin(z, a).mul(lin(z, b)))
                }) == Fp::ZERO
            })
            && self
                .lookups
                .iter()
                .all(|l| l.f.iter().all(|&i| l.table.contains(&Fp(z[i]))))
    }
    /// `T`: the maximum number of product terms in a row.
    pub fn width(&self) -> usize {
        self.rows.iter().map(|r| r.prods.len()).max().unwrap_or(0)
    }
    /// `ℓ ≥ 1` with `rows ≤ 2^ℓ`.
    pub fn log_rows(&self) -> usize {
        let mut l = 1;
        while (1usize << l) < self.rows.len() {
            l += 1;
        }
        l
    }
    /// Canonical, length-prefixed instance encoding for the transcript.
    pub fn digest(&self) -> [u8; 32] {
        let mut h = Sha3_256::new();
        h.update(b"minidregg.svcs.instance.v1");
        let form = |h: &mut Sha3_256, f: &LinForm| {
            h.update((f.len() as u64).to_le_bytes());
            for &(c, w) in f {
                h.update(c.0.to_le_bytes());
                h.update((w as u64).to_le_bytes());
            }
        };
        h.update((self.n_z as u64).to_le_bytes());
        h.update((self.rows.len() as u64).to_le_bytes());
        for r in &self.rows {
            h.update((r.prods.len() as u64).to_le_bytes());
            for (a, b) in &r.prods {
                form(&mut h, a);
                form(&mut h, b);
            }
            form(&mut h, &r.c);
        }
        h.update((self.lookups.len() as u64).to_le_bytes());
        for l in &self.lookups {
            h.update((l.f.len() as u64).to_le_bytes());
            for &i in &l.f {
                h.update((i as u64).to_le_bytes());
            }
            h.update((l.table.len() as u64).to_le_bytes());
            for t in &l.table {
                h.update(t.0.to_le_bytes());
            }
        }
        h.finalize().into()
    }
}

/// Witness binding (oracle model: binding, not hiding).
pub fn witness_digest(z: &[u32]) -> [u8; 32] {
    let mut h = Sha3_256::new();
    h.update(b"minidregg.svcs.witness.v1");
    h.update((z.len() as u64).to_le_bytes());
    for v in z {
        h.update(v.to_le_bytes());
    }
    h.finalize().into()
}

// ─────────────────────────────── §4. Transcript ───────────────────────────────

/// SHA3-256 chained transcript. Every absorb/squeeze is framed as
/// `opcode ‖ state ‖ len(tag) ‖ tag ‖ len(msg) ‖ msg` with distinct one-byte opcodes, so no two
/// (opcode, tag, message) sequences share an encoding.
#[derive(Clone)]
struct Transcript {
    state: [u8; 32],
}

impl Transcript {
    fn new(inst: &SvcsInstance, wdig: &[u8; 32], context: &[u8]) -> Self {
        let mut t = Transcript { state: [0u8; 32] };
        t.absorb(b"svcs/v2/domain", b"minidregg.svcs.zerocheck+logup.v2");
        t.absorb(b"svcs/v2/session", context);
        t.absorb(b"svcs/v2/instance", &inst.digest());
        t.absorb(b"svcs/v2/witness", wdig);
        t
    }
    pub fn absorb(&mut self, tag: &[u8], msg: &[u8]) {
        let mut h = Sha3_256::new();
        h.update(b"A");
        h.update(self.state);
        h.update((tag.len() as u64).to_le_bytes());
        h.update(tag);
        h.update((msg.len() as u64).to_le_bytes());
        h.update(msg);
        self.state = h.finalize().into();
    }
    pub fn absorb_ext(&mut self, tag: &[u8], xs: &[Ext4]) {
        let mut b = Vec::with_capacity(16 * xs.len());
        for x in xs {
            for c in x.0 {
                b.extend_from_slice(&c.to_le_bytes());
            }
        }
        self.absorb(tag, &b);
    }
    /// Each accepted 32-bit word lies in [0, 2p), so both representatives have equal mass.
    fn squeeze(&mut self, tag: &[u8]) -> Ext4 {
        let mut result = [0; 4];
        let mut filled = 0;
        while filled < 4 {
            let block = cshake256_xof(tag, &self.state, 32);
            self.absorb(b"svcs/v2/challenge-block", &block);
            for word in block.chunks_exact(4) {
                let v = u32::from_le_bytes(word.try_into().unwrap());
                if v < 2 * P {
                    result[filled] = v % P;
                    filled += 1;
                    if filled == 4 {
                        break;
                    }
                }
            }
        }
        Ext4(result)
    }
    fn lookup_point(&mut self) -> Ext4 {
        loop {
            let x = self.squeeze(b"svcs/v2/logup/alpha");
            if x.0[1..] != [0; 3] {
                return x;
            }
        }
    }
}

// ─────────────────────────────── §5. Proofs ───────────────────────────────

#[derive(Clone, Debug, PartialEq)]
pub struct LookupProof {
    pub mult: Vec<u32>,
    pub root: [Ext4; 2],
    pub layers: Vec<LayerProof>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct SvcsProof {
    pub repetitions: [PassProof; 2],
    pub transcript_digest: [u8; 32],
}

#[derive(Clone, Debug, PartialEq)]
pub struct PassProof {
    /// `s_j(0), s_j(1), s_j(2), s_j(3)` per round.
    pub rounds: Vec<[Ext4; 4]>,
    /// `ã_0(r), b̃_0(r), …, ã_{T-1}(r), b̃_{T-1}(r), c̃(r)`.
    pub terminal: Vec<Ext4>,
    pub lookups: Vec<LookupProof>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProverMode {
    NaiveExt,
    SmallValueGruen,
}

/// Prover statistics (which small-value accumulator was used, validated tags).
#[derive(Clone, Debug, Default)]
pub struct ProverStats {
    pub round0_i64: bool,
    pub round1_i64: bool,
    pub tags_valid: usize,
    pub tags_rejected: usize,
}

/// Row tables `a_t(k), b_t(k)` for `t < T` and `c(k)`, zero-padded to `2^ℓ` rows.
struct Tables {
    a: Vec<Vec<Fp>>,
    b: Vec<Vec<Fp>>,
    c: Vec<Fp>,
}

fn row_tables(inst: &SvcsInstance, z: &[u32], ell: usize) -> Tables {
    let n = 1usize << ell;
    let t = inst.width();
    let mut tb = Tables {
        a: vec![vec![Fp::ZERO; n]; t],
        b: vec![vec![Fp::ZERO; n]; t],
        c: vec![Fp::ZERO; n],
    };
    for (k, r) in inst.rows.iter().enumerate() {
        for (ti, (fa, fb)) in r.prods.iter().enumerate() {
            tb.a[ti][k] = lin(z, fa);
            tb.b[ti][k] = lin(z, fb);
        }
        tb.c[k] = lin(z, &r.c);
    }
    tb
}

fn fold_ext(v: &[Ext4], r: Ext4) -> Vec<Ext4> {
    (0..v.len() / 2)
        .map(|k| v[2 * k].add(r.mul(v[2 * k + 1].sub(v[2 * k]))))
        .collect()
}

fn fold_base(v: &[Fp], r: Ext4) -> Vec<Ext4> {
    (0..v.len() / 2)
        .map(|k| Ext4::from_base(v[2 * k]).add(r.mul_base(v[2 * k + 1].sub(v[2 * k]))))
        .collect()
}

/// Gruen: `s(X) = L·eq(τ_j, X)·t(X)` with `t` quadratic from `t(0), t(1), t(∞)`.
fn gruen_evals(l: Ext4, tau_j: Ext4, t0: Ext4, t1: Ext4, tinf: Ext4) -> [Ext4; 4] {
    let lin_c = t1.sub(t0).sub(tinf);
    let mut out = [Ext4::ZERO; 4];
    for (x, o) in out.iter_mut().enumerate() {
        let xe = Ext4::from_base(Fp(x as u32));
        let tx = t0.add(lin_c.mul(xe)).add(tinf.mul(xe.mul(xe)));
        *o = l.mul(eq1(tau_j, xe)).mul(tx);
    }
    out
}

/// Maximum absolute row values before eq weighting, for both accumulator widths.
fn accumulator_limits(terms: usize) -> (i128, i128) {
    let weight = (P as i128 - 1) * terms as i128;
    (i64::MAX as i128 / weight, i128::MAX / weight)
}

/// Small-value round 0 (2026/587 §5.1 + §3.3): exact integer row values, `eq` split as
/// `eqL ⊗ eqR`, inner sums accumulated per `Ext4` coordinate WITHOUT modular reduction, one
/// reduction per outer index when the signed bound permits. Returns `(t(0), t(1), t(∞), used_i64)`.
fn round0_small(tb: &Tables, eq_l: &[Ext4], eq_r: &[Ext4], h: usize) -> (Ext4, Ext4, Ext4, bool) {
    let half = tb.c.len() / 2;
    let width = tb.a.len();
    // Exact integers from signed representatives: |a|,|b|,|c| < 2^30, so each product < 2^60 and
    // each difference product is below 2^62. With usize at most 64 bits even
    // their sum is below 2^126. Test the separate eq-weighted budget before multiplying.
    let val = |k: usize| -> i128 {
        let mut s = tb.c[k].signed() as i128;
        for t in 0..width {
            s += tb.a[t][k].signed() as i128 * tb.b[t][k].signed() as i128;
        }
        s
    };
    let dinf = |k: usize| -> i128 {
        let mut s = 0i128;
        for t in 0..width {
            let da = tb.a[t][2 * k + 1].signed() as i128 - tb.a[t][2 * k].signed() as i128;
            let db = tb.b[t][2 * k + 1].signed() as i128 - tb.b[t][2 * k].signed() as i128;
            s += da * db;
        }
        s
    };
    debug_assert_eq!(half, eq_l.len() * eq_r.len());
    let mut v0 = Vec::with_capacity(half);
    let mut v1 = Vec::with_capacity(half);
    let mut vi = Vec::with_capacity(half);
    let mut bound: i128 = 0;
    for k in 0..half {
        let (a, b, c) = (val(2 * k), val(2 * k + 1), dinf(k));
        bound = bound.max(a.abs()).max(b.abs()).max(c.abs());
        v0.push(a);
        v1.push(b);
        vi.push(c);
    }
    let (limit64, limit128) = accumulator_limits(eq_l.len());
    let use_i64 = bound <= limit64;
    if bound > limit128 {
        // reduce row values to signed representatives: |x| < 2^30, so 2^h·2^31·2^30 < 2^127
        // for every h < 66.
        for v in [&mut v0, &mut v1, &mut vi] {
            for x in v.iter_mut() {
                *x = Fp::from_i128(*x).signed() as i128;
            }
        }
    }
    let reduce = |acc: [i128; 4]| Ext4(acc.map(|x| Fp::from_i128(x).0));
    let (mut t0, mut t1, mut ti) = (Ext4::ZERO, Ext4::ZERO, Ext4::ZERO);
    for (khi, &er) in eq_r.iter().enumerate() {
        let base = khi << h;
        let (mut a0, mut a1, mut ai) = ([0i128; 4], [0i128; 4], [0i128; 4]);
        if use_i64 {
            let (mut b0, mut b1, mut bi) = ([0i64; 4], [0i64; 4], [0i64; 4]);
            for (klo, el) in eq_l.iter().enumerate() {
                let k = base + klo;
                let (x0, x1, xi) = (v0[k] as i64, v1[k] as i64, vi[k] as i64);
                for c in 0..4 {
                    let e = el.0[c] as i64;
                    b0[c] += e * x0;
                    b1[c] += e * x1;
                    bi[c] += e * xi;
                }
            }
            for c in 0..4 {
                a0[c] = b0[c] as i128;
                a1[c] = b1[c] as i128;
                ai[c] = bi[c] as i128;
            }
        } else {
            for (klo, el) in eq_l.iter().enumerate() {
                let k = base + klo;
                for c in 0..4 {
                    let e = el.0[c] as i128;
                    a0[c] += e * v0[k];
                    a1[c] += e * v1[k];
                    ai[c] += e * vi[k];
                }
            }
        }
        t0 = t0.add(er.mul(reduce(a0)));
        t1 = t1.add(er.mul(reduce(a1)));
        ti = ti.add(er.mul(reduce(ai)));
    }
    (t0, t1, ti, use_i64)
}

/// Extension-field Gruen round with split `eq`: returns `(t(0), t(∞))`.
fn round_ext_gruen(
    a: &[Vec<Ext4>],
    b: &[Vec<Ext4>],
    c: &[Ext4],
    eq_l: &[Ext4],
    eq_r: &[Ext4],
    h: usize,
) -> (Ext4, Ext4) {
    let (mut t0, mut ti) = (Ext4::ZERO, Ext4::ZERO);
    for (khi, &er) in eq_r.iter().enumerate() {
        let (mut i0, mut ii) = (Ext4::ZERO, Ext4::ZERO);
        for (klo, &el) in eq_l.iter().enumerate() {
            let k = klo + (khi << h);
            let (e, o) = (2 * k, 2 * k + 1);
            let mut f0 = c[e];
            let mut d = Ext4::ZERO;
            for t in 0..a.len() {
                f0 = f0.add(a[t][e].mul(b[t][e]));
                d = d.add(a[t][o].sub(a[t][e]).mul(b[t][o].sub(b[t][e])));
            }
            i0 = i0.add(el.mul(f0));
            ii = ii.add(el.mul(d));
        }
        t0 = t0.add(er.mul(i0));
        ti = ti.add(er.mul(ii));
    }
    (t0, ti)
}

/// Direct `t(1)` (fallback when `τ_j = 0` or `L = 0` makes the Gruen derivation singular).
fn round_ext_t1(a: &[Vec<Ext4>], b: &[Vec<Ext4>], c: &[Ext4], eqr: &[Ext4]) -> Ext4 {
    let mut s = Ext4::ZERO;
    for (k, &e) in eqr.iter().enumerate() {
        let o = 2 * k + 1;
        let mut f = c[o];
        for t in 0..a.len() {
            f = f.add(a[t][o].mul(b[t][o]));
        }
        s = s.add(e.mul(f));
    }
    s
}

fn split_eq(tau_rest: &[Ext4]) -> (Vec<Ext4>, Vec<Ext4>, usize) {
    let h = tau_rest.len() / 2;
    (eq_table(&tau_rest[..h]), eq_table(&tau_rest[h..]), h)
}

/// `t(1) = (claim/L - (1-τ)·t(0)) / τ`; `None` when singular.
fn gruen_t1(claim: Ext4, l: Ext4, tau: Ext4, t0: Ext4) -> Option<Ext4> {
    let li = l.inv()?;
    let ti = tau.inv()?;
    Some(claim.mul(li).sub(Ext4::ONE.sub(tau).mul(t0)).mul(ti))
}

/// LogUp multiplicities: count of `z_{f_i}` per FIRST occurrence in the table.
fn multiplicities(l: &Lookup, z: &[u32]) -> Vec<u32> {
    let mut m = vec![0u32; l.table.len()];
    let mut index = std::collections::HashMap::new();
    for (j, v) in l.table.iter().enumerate() {
        index.entry(v.0).or_insert(j);
    }
    for &i in &l.f {
        if let Some(&j) = index.get(&z[i]) {
            m[j] += 1;
        }
    }
    m
}

/// Entries with zero numerator and denominator one pad arbitrary finite tables.
type Fraction = [Ext4; 2];

fn leaves(l: &Lookup, z: &[u32], mult: &[u32], alpha: Ext4) -> Vec<Fraction> {
    let side = l.f.len().max(l.table.len()).next_power_of_two();
    let mut v = vec![[Ext4::ZERO, Ext4::ONE]; 2 * side];
    for (out, &i) in v.iter_mut().zip(&l.f) {
        *out = [Ext4::ONE, alpha.sub(Ext4::from_bb(z[i]))];
    }
    for (out, (&t, &m)) in v[side..].iter_mut().zip(l.table.iter().zip(mult)) {
        *out = [Ext4::from_bb(m).neg(), alpha.sub(Ext4::from_base(t))];
    }
    v
}

fn combine([a, b]: Fraction, [c, d]: Fraction) -> Fraction {
    [a.mul(d).add(c.mul(b)), b.mul(d)]
}

fn lerp(a: Ext4, b: Ext4, t: Ext4) -> Ext4 {
    a.add(t.mul(b.sub(a)))
}

fn layer_value([a, b, c, d]: [Ext4; 4], beta: Ext4) -> Ext4 {
    let [num, den] = combine([a, b], [c, d]);
    num.add(beta.mul(den))
}

#[derive(Clone, Debug, PartialEq)]
pub struct LayerProof {
    pub rounds: Vec<[Ext4; 4]>,
    pub children: [Ext4; 4],
}

/// Reduce the two evaluations at (0,r) and (1,r) to one evaluation at (s,r).
fn bind_children(tr: &mut Transcript, point: &mut Vec<Ext4>, children: [Ext4; 4]) -> Fraction {
    tr.absorb_ext(b"svcs/v2/logup/children", &children);
    let s = tr.squeeze(b"svcs/v2/logup/branch");
    point.insert(0, s);
    [
        lerp(children[0], children[2], s),
        lerp(children[1], children[3], s),
    ]
}

fn layer_challenge(tr: &mut Transcript, msg: &[Ext4; 4]) -> Ext4 {
    tr.absorb_ext(b"svcs/v2/logup/layer/round", msg);
    tr.squeeze(b"svcs/v2/logup/layer/point")
}

fn prove_tree(tr: &mut Transcript, leaf: Vec<Fraction>, mult: Vec<u32>) -> LookupProof {
    let mut levels = vec![leaf];
    while levels.last().unwrap().len() > 1 {
        let parents = levels
            .last()
            .unwrap()
            .chunks_exact(2)
            .map(|p| combine(p[0], p[1]))
            .collect();
        levels.push(parents);
    }
    let root = levels.pop().unwrap()[0];
    tr.absorb_ext(b"svcs/v2/logup/root", &root);
    let mut point = Vec::new();
    let mut layers = Vec::new();
    for level in levels.iter().rev() {
        let beta = tr.squeeze(b"svcs/v2/logup/batch");
        let mut eq = eq_table(&point);
        let mut columns: [Vec<_>; 4] = std::array::from_fn(|i| {
            level
                .chunks_exact(2)
                .map(|pair| pair[i / 2][i % 2])
                .collect()
        });
        let mut rounds = Vec::with_capacity(point.len());
        point.clear();
        while eq.len() > 1 {
            let msg = [0, 1, 2, 3].map(|x| {
                let t = Ext4::from_bb(x);
                (0..eq.len() / 2).fold(Ext4::ZERO, |acc, i| {
                    let eval = |v: &[Ext4]| lerp(v[2 * i], v[2 * i + 1], t);
                    acc.add(eval(&eq).mul(layer_value(
                        std::array::from_fn(|k| eval(&columns[k])),
                        beta,
                    )))
                })
            });
            let r = layer_challenge(tr, &msg);
            point.push(r);
            rounds.push(msg);
            eq = fold_ext(&eq, r);
            columns = columns.map(|v| fold_ext(&v, r));
        }
        let children = columns.map(|v| v[0]);
        bind_children(tr, &mut point, children);
        layers.push(LayerProof { rounds, children });
    }
    LookupProof { mult, root, layers }
}

fn verify_tree(tr: &mut Transcript, proof: &LookupProof, leaf: &[Fraction]) -> Result<(), String> {
    let mut claim = proof.root;
    if !claim.iter().all(|v| v.is_canonical()) || claim[0] != Ext4::ZERO || claim[1] == Ext4::ZERO {
        return Err("invalid projective LogUp root".into());
    }
    if proof.layers.len() != leaf.len().ilog2() as usize {
        return Err("LogUp depth mismatch".into());
    }
    tr.absorb_ext(b"svcs/v2/logup/root", &claim);
    let mut point = Vec::new();
    for layer in &proof.layers {
        if layer.rounds.len() != point.len() || !layer.children.iter().all(|v| v.is_canonical()) {
            return Err("invalid LogUp layer".into());
        }
        let beta = tr.squeeze(b"svcs/v2/logup/batch");
        let mut sum = claim[0].add(beta.mul(claim[1]));
        let mut eq = Ext4::ONE;
        for (u, msg) in point.iter_mut().zip(&layer.rounds) {
            if !msg.iter().all(|v| v.is_canonical()) || msg[0].add(msg[1]) != sum {
                return Err("LogUp layer round sum mismatch".into());
            }
            let r = layer_challenge(tr, msg);
            eq = eq.mul(eq1(*u, r));
            sum = interp4(msg, r);
            *u = r;
        }
        if sum != eq.mul(layer_value(layer.children, beta)) {
            return Err("LogUp layer evaluation mismatch".into());
        }
        claim = bind_children(tr, &mut point, layer.children);
    }
    let mut opened = [Ext4::ZERO; 2];
    for (weight, pair) in eq_table(&point).into_iter().zip(leaf) {
        for k in 0..2 {
            opened[k] = opened[k].add(weight.mul(pair[k]));
        }
    }
    if claim != opened {
        return Err("LogUp leaf oracle mismatch".into());
    }
    Ok(())
}

fn absorb_mult(tr: &mut Transcript, m: &[u32]) {
    let mb: Vec<u8> = m.iter().flat_map(|x| x.to_le_bytes()).collect();
    tr.absorb(b"svcs/v2/logup/mult", &mb);
}

/// The one generic prover.
pub struct SvcsProver;

impl SvcsProver {
    pub fn prove(inst: &SvcsInstance, z: &[u32], mode: ProverMode) -> Result<SvcsProof, String> {
        Self::prove_with_stats(inst, z, &[], mode).map(|(p, _)| p)
    }

    pub fn prove_with_stats(
        inst: &SvcsInstance,
        z: &[u32],
        tags: &[(usize, Lane)],
        mode: ProverMode,
    ) -> Result<(SvcsProof, ProverStats), String> {
        Self::prove_in_context(inst, z, tags, mode, b"")
    }

    pub fn prove_in_context(
        inst: &SvcsInstance,
        z: &[u32],
        tags: &[(usize, Lane)],
        mode: ProverMode,
        context: &[u8],
    ) -> Result<(SvcsProof, ProverStats), String> {
        inst.validate(z)?;
        let mut stats = ProverStats::default();
        for &(j, lane) in tags {
            if j < z.len() && lane.admits(z[j]) {
                stats.tags_valid += 1;
            } else {
                stats.tags_rejected += 1;
            }
        }
        let ell = inst.log_rows();
        let tb = row_tables(inst, z, ell);
        let mut tr = Transcript::new(inst, &witness_digest(z), context);
        let first = Self::pass(inst, z, mode, &tb, &mut stats, &mut tr);
        let second = Self::pass(inst, z, mode, &tb, &mut stats, &mut tr);
        Ok((
            SvcsProof {
                repetitions: [first, second],
                transcript_digest: tr.state,
            },
            stats,
        ))
    }

    fn pass(
        inst: &SvcsInstance,
        z: &[u32],
        mode: ProverMode,
        tb: &Tables,
        stats: &mut ProverStats,
        tr: &mut Transcript,
    ) -> PassProof {
        tr.absorb(b"svcs/v2/repetition", b"begin");
        let ell = inst.log_rows();
        let tau: Vec<Ext4> = (0..ell).map(|_| tr.squeeze(b"svcs/v2/zc/tau")).collect();
        let mut rounds = Vec::with_capacity(ell);
        let (mut a, mut b, mut c): (Vec<Vec<Ext4>>, Vec<Vec<Ext4>>, Vec<Ext4>);
        match mode {
            ProverMode::NaiveExt => {
                let lift = |v: &Vec<Fp>| v.iter().map(|&x| Ext4::from_base(x)).collect::<Vec<_>>();
                a = tb.a.iter().map(lift).collect();
                b = tb.b.iter().map(lift).collect();
                c = lift(&tb.c);
                let mut e = eq_table(&tau);
                let xs = [0u32, 1, 2, 3].map(|x| Ext4::from_base(Fp(x)));
                for _ in 0..ell {
                    let mut s = [Ext4::ZERO; 4];
                    for k in 0..c.len() / 2 {
                        let (lo, hi) = (2 * k, 2 * k + 1);
                        for (x, sx) in s.iter_mut().enumerate() {
                            let at = |v: &Vec<Ext4>| v[lo].add(xs[x].mul(v[hi].sub(v[lo])));
                            let mut f = at(&c);
                            for t in 0..a.len() {
                                f = f.add(at(&a[t]).mul(at(&b[t])));
                            }
                            *sx = sx.add(at(&e).mul(f));
                        }
                    }
                    tr.absorb_ext(b"svcs/v2/zc/round", &s);
                    let r = tr.squeeze(b"svcs/v2/zc/challenge");
                    rounds.push(s);
                    e = fold_ext(&e, r);
                    a = a.iter().map(|v| fold_ext(v, r)).collect();
                    b = b.iter().map(|v| fold_ext(v, r)).collect();
                    c = fold_ext(&c, r);
                }
            }
            ProverMode::SmallValueGruen => {
                let mut l_pref = Ext4::ONE;
                // round 0 on base-field integers (small-value + delayed reduction)
                let (eq_l, eq_r, h) = split_eq(&tau[1..]);
                let (t0, t1, tinf, used) = round0_small(tb, &eq_l, &eq_r, h);
                stats.round0_i64 = used;
                let s = gruen_evals(l_pref, tau[0], t0, t1, tinf);
                tr.absorb_ext(b"svcs/v2/zc/round", &s);
                let r = tr.squeeze(b"svcs/v2/zc/challenge");
                rounds.push(s);
                let mut claim = interp4(&s, r);
                l_pref = l_pref.mul(eq1(tau[0], r));
                let mut bind = vec![r];
                if ell >= 2 {
                    let (el, er, h) = split_eq(&tau[2..]);
                    // The residual is quadratic in the first variable. At x=0,1,2 we
                    // still have base-field columns, including for wide signed inputs.
                    let mut samples = [[Ext4::ZERO; 3]; 3];
                    let mut narrow = true;
                    for (x, sample) in samples.iter_mut().enumerate() {
                        let at = |v: &[Fp]| {
                            v.chunks_exact(2)
                                .map(|p| match x {
                                    0 => p[0],
                                    1 => p[1],
                                    _ => p[1].add(p[1]).sub(p[0]),
                                })
                                .collect()
                        };
                        let base = Tables {
                            a: tb.a.iter().map(|v| at(v)).collect(),
                            b: tb.b.iter().map(|v| at(v)).collect(),
                            c: at(&tb.c),
                        };
                        let (v0, v1, vi, small) = round0_small(&base, &el, &er, h);
                        *sample = [v0, v1, vi];
                        narrow &= small;
                    }
                    stats.round1_i64 = narrow;
                    let values = [0, 1, 2].map(|i| {
                        let [v0, v1, v2] = samples.map(|s| s[i]);
                        let quadratic = v2.sub(v1.add(v1)).add(v0).scale_bb(babybear::HALF as u32);
                        v0.add(r.mul(v1.sub(v0).add(r.sub(Ext4::ONE).mul(quadratic))))
                    });
                    let s = gruen_evals(l_pref, tau[1], values[0], values[1], values[2]);
                    tr.absorb_ext(b"svcs/v2/zc/round", &s);
                    let r1 = tr.squeeze(b"svcs/v2/zc/challenge");
                    rounds.push(s);
                    claim = interp4(&s, r1);
                    l_pref = l_pref.mul(eq1(tau[1], r1));
                    bind.push(r1);
                }
                let promote = |v: &[Fp]| {
                    if bind.len() == 1 {
                        return fold_base(v, r);
                    }
                    v.chunks_exact(4)
                        .map(|p| {
                            let left = Ext4::from_base(p[0]).add(r.mul_base(p[1].sub(p[0])));
                            let right = Ext4::from_base(p[2]).add(r.mul_base(p[3].sub(p[2])));
                            left.add(bind[1].mul(right.sub(left)))
                        })
                        .collect()
                };
                a = tb.a.iter().map(|v| promote(v)).collect();
                b = tb.b.iter().map(|v| promote(v)).collect();
                c = promote(&tb.c);
                for j in bind.len()..ell {
                    let (eq_l, eq_r, h) = split_eq(&tau[j + 1..]);
                    let (t0, tinf) = round_ext_gruen(&a, &b, &c, &eq_l, &eq_r, h);
                    let t1 = match gruen_t1(claim, l_pref, tau[j], t0) {
                        Some(t1) => t1,
                        None => round_ext_t1(&a, &b, &c, &eq_table(&tau[j + 1..])),
                    };
                    let s = gruen_evals(l_pref, tau[j], t0, t1, tinf);
                    tr.absorb_ext(b"svcs/v2/zc/round", &s);
                    let r = tr.squeeze(b"svcs/v2/zc/challenge");
                    rounds.push(s);
                    claim = interp4(&s, r);
                    l_pref = l_pref.mul(eq1(tau[j], r));
                    a = a.iter().map(|v| fold_ext(v, r)).collect();
                    b = b.iter().map(|v| fold_ext(v, r)).collect();
                    c = fold_ext(&c, r);
                }
            }
        }
        let mut terminal = Vec::with_capacity(2 * a.len() + 1);
        for t in 0..a.len() {
            terminal.push(a[t][0]);
            terminal.push(b[t][0]);
        }
        terminal.push(c[0]);
        tr.absorb_ext(b"svcs/v2/terminal", &terminal);
        let _gamma = tr.squeeze(b"svcs/v2/terminal/gamma");
        let mut lookups = Vec::with_capacity(inst.lookups.len());
        for l in &inst.lookups {
            let mult = multiplicities(l, z);
            absorb_mult(tr, &mult);
            let alpha = tr.lookup_point();
            let leaf = leaves(l, z, &mult, alpha);
            lookups.push(prove_tree(tr, leaf, mult));
        }
        PassProof {
            rounds,
            terminal,
            lookups,
        }
    }
}

/// The one generic verifier (oracle access to `z` for terminal and LogUp claims).
pub struct SvcsVerifier;

impl SvcsVerifier {
    pub fn verify(inst: &SvcsInstance, z: &[u32], proof: &SvcsProof) -> Result<(), String> {
        Self::verify_in_context(inst, z, proof, b"")
    }

    pub fn verify_in_context(
        inst: &SvcsInstance,
        z: &[u32],
        proof: &SvcsProof,
        context: &[u8],
    ) -> Result<(), String> {
        inst.validate(z)?;
        let mut tr = Transcript::new(inst, &witness_digest(z), context);
        for pass in &proof.repetitions {
            Self::pass(inst, z, pass, &mut tr)?;
        }
        if proof.transcript_digest != tr.state {
            return Err("transcript binding mismatch".into());
        }
        Ok(())
    }

    fn pass(
        inst: &SvcsInstance,
        z: &[u32],
        proof: &PassProof,
        tr: &mut Transcript,
    ) -> Result<(), String> {
        tr.absorb(b"svcs/v2/repetition", b"begin");
        let ell = inst.log_rows();
        let width = inst.width();
        if proof.rounds.len() != ell || proof.terminal.len() != 2 * width + 1 {
            return Err("proof shape mismatch".into());
        }
        if proof.lookups.len() != inst.lookups.len() {
            return Err("lookup proof count mismatch".into());
        }
        let canon = |x: &Ext4| x.0.iter().all(|&c| c < P);
        if !proof.rounds.iter().flatten().all(canon) || !proof.terminal.iter().all(canon) {
            return Err("non-canonical proof element".into());
        }
        let tau: Vec<Ext4> = (0..ell).map(|_| tr.squeeze(b"svcs/v2/zc/tau")).collect();
        let mut claim = Ext4::ZERO;
        let mut r = Vec::with_capacity(ell);
        for (j, s) in proof.rounds.iter().enumerate() {
            if s[0].add(s[1]) != claim {
                return Err(format!("round {j}: s(0)+s(1) != claim"));
            }
            tr.absorb_ext(b"svcs/v2/zc/round", s);
            let rj = tr.squeeze(b"svcs/v2/zc/challenge");
            claim = interp4(s, rj);
            r.push(rj);
        }
        let mut f = proof.terminal[2 * width];
        for t in 0..width {
            f = f.add(proof.terminal[2 * t].mul(proof.terminal[2 * t + 1]));
        }
        let eq_tr = tau
            .iter()
            .zip(&r)
            .fold(Ext4::ONE, |acc, (&t, &x)| acc.mul(eq1(t, x)));
        if claim != eq_tr.mul(f) {
            return Err("final zerocheck claim mismatch".into());
        }
        tr.absorb_ext(b"svcs/v2/terminal", &proof.terminal);
        let gamma = tr.squeeze(b"svcs/v2/terminal/gamma");
        // γ-batched terminal check: ONE eq(r,·) pass over Σ_i γ^i table_i (the oracle read).
        let eqr = eq_table(&r);
        let mut gp = vec![Ext4::ONE; 2 * width + 1];
        for i in 1..gp.len() {
            gp[i] = gp[i - 1].mul(gamma);
        }
        let mut lhs = Ext4::ZERO;
        for (row, e) in inst.rows.iter().zip(eqr) {
            let mut v = gp[2 * width].mul_base(lin(z, &row.c));
            for (t, (a, b)) in row.prods.iter().enumerate() {
                v = v
                    .add(gp[2 * t].mul_base(lin(z, a)))
                    .add(gp[2 * t + 1].mul_base(lin(z, b)));
            }
            lhs = lhs.add(e.mul(v));
        }
        let rhs = proof
            .terminal
            .iter()
            .zip(&gp)
            .fold(Ext4::ZERO, |acc, (&v, &g)| acc.add(g.mul(v)));
        if lhs != rhs {
            return Err("batched terminal evaluation claim mismatch".into());
        }
        for (li, (l, lp)) in inst.lookups.iter().zip(&proof.lookups).enumerate() {
            if lp.mult.len() != l.table.len() || lp.mult.iter().any(|&m| m >= P) {
                return Err(format!("lookup {li}: malformed multiplicities"));
            }
            if lp
                .mult
                .iter()
                .try_fold(0usize, |a, &m| a.checked_add(m as usize))
                != Some(l.f.len())
            {
                return Err(format!("lookup {li}: multiplicity count mismatch"));
            }
            absorb_mult(tr, &lp.mult);
            let alpha = tr.lookup_point();
            verify_tree(tr, lp, &leaves(l, z, &lp.mult, alpha))?;
            // Discharge the membership premise of the Lean row theorem against this oracle.
            if lp.mult != multiplicities(l, z) {
                return Err("lookup histogram mismatch".into());
            }
        }
        Ok(())
    }
}

// ─────────────────────────────── §6. Unit tests ───────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    fn e(a: u32, b: u32, c: u32, d: u32) -> Ext4 {
        Ext4([a, b, c, d])
    }

    #[test]
    fn ext4_field_laws() {
        assert_eq!(
            babybear::bpow(W.into(), (babybear::P - 1) / 2),
            babybear::P - 1
        );
        let x = e(3, 1_000_000_007 % P, 5, P - 1);
        let y = e(17, 0, 2, 9);
        assert_eq!(x.mul(y), y.mul(x));
        assert_eq!(x.mul(x.inv().unwrap()), Ext4::ONE);
        let u = e(0, 1, 0, 0);
        assert_eq!(u.mul(u).mul(u).mul(u), Ext4::from_base(Fp(11)));
        assert_eq!(Ext4::ZERO.inv(), None);
    }

    #[test]
    fn eq_table_sums_to_one_and_interp_is_exact() {
        let tau = [e(5, 1, 0, 2), e(7, 0, 3, 0), e(11, 4, 4, 4)];
        let t = eq_table(&tau);
        assert_eq!(t.iter().fold(Ext4::ZERO, |a, &x| a.add(x)), Ext4::ONE);
        let p = |x: Ext4| {
            x.mul(x)
                .mul(x)
                .add(x.mul_base(Fp(2)))
                .add(Ext4::from_base(Fp(5)))
        };
        let ev = [0u32, 1, 2, 3].map(|v| p(Ext4::from_base(Fp(v))));
        let x = e(123, 456, 789, 1011);
        assert_eq!(interp4(&ev, x), p(x));
    }

    #[test]
    fn json_minimal() {
        let j = parse_json("{\"a\":[1,-2,{\"b\":true}],\"s\":\"x\"}").unwrap();
        assert_eq!(j.get("a").unwrap().arr().unwrap()[1], Json::Num(-2));
        assert!(parse_json("[1,]").is_err());
        assert!(parse_json("[1.5]").is_err());
        assert!(parse_json(r#"{"a":1,"a":2}"#).is_err());
        assert_eq!(
            parse_json(r#""\uD83D\uDC3B""#).unwrap().str().unwrap(),
            "🐻"
        );
    }

    #[test]
    fn delayed_reduction_boundaries() {
        for terms in [1, 2, 17, 256, 65536, usize::MAX] {
            let weight = (P as i128 - 1) * terms as i128;
            let (small, wide) = accumulator_limits(terms);
            assert!(small * weight <= i64::MAX as i128);
            assert!((small + 1) * weight > i64::MAX as i128);
            assert!(wide.checked_mul(weight).is_some());
            assert!((wide + 1).checked_mul(weight).is_none());
        }
        assert!(gruen_t1(Ext4::ONE, Ext4::ZERO, Ext4::ONE, Ext4::ZERO).is_none());
        assert!(gruen_t1(Ext4::ONE, Ext4::ONE, Ext4::ZERO, Ext4::ZERO).is_none());
    }

    #[test]
    fn tiny_instance_naive_equals_small_value() {
        // z = [1, 3, 4, 12, 7]: rows z1*z2 - z3 = 0, z1 + z2 - z4 = 0, z4 ∈ {7, 9}
        let inst = SvcsInstance {
            n_z: 5,
            rows: vec![
                Row {
                    prods: vec![(vec![(Fp(1), 1)], vec![(Fp(1), 2)])],
                    c: vec![(Fp(P - 1), 3)],
                },
                Row {
                    prods: vec![],
                    c: vec![(Fp(1), 1), (Fp(1), 2), (Fp(P - 1), 4)],
                },
                Row {
                    prods: vec![],
                    c: vec![],
                },
            ],
            lookups: vec![Lookup {
                f: vec![4],
                table: vec![Fp(7), Fp(9)],
            }],
        };
        let z = [1, 3, 4, 12, 7];
        assert!(inst.satisfied(&z));
        let p1 = SvcsProver::prove(&inst, &z, ProverMode::NaiveExt).unwrap();
        let p2 = SvcsProver::prove(&inst, &z, ProverMode::SmallValueGruen).unwrap();
        assert_eq!(p1, p2);
        SvcsVerifier::verify(&inst, &z, &p1).unwrap();
        let bad = [1, 3, 4, 13, 7];
        let p3 = SvcsProver::prove(&inst, &bad, ProverMode::NaiveExt).unwrap();
        assert!(SvcsVerifier::verify(&inst, &bad, &p3).is_err());
        let p4 = SvcsProver::prove(&inst, &bad, ProverMode::SmallValueGruen).unwrap();
        assert!(SvcsVerifier::verify(&inst, &bad, &p4).is_err());
    }
}
