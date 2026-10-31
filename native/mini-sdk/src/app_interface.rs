//! One declaration supplies native typed calls, tool schemas and qualification.
//! This layer encodes application data. Admission and exact dispatch receipts remain
//! the existing Mini application receiver's responsibility. Never retry a mutation.
use crate::app_interface_cookie::CookieJar;
use base64::{engine::general_purpose::STANDARD, Engine};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Refusal {
    pub name: String,
    pub uncertain: bool,
}
pub type Result<T> = std::result::Result<T, Refusal>;
fn refuse(name: &str) -> Refusal {
    Refusal {
        name: name.into(),
        uncertain: false,
    }
}
impl std::fmt::Display for Refusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.name)
    }
}
impl std::error::Error for Refusal {}
#[derive(Clone, Debug)]
pub struct PreparedCall {
    pub method: String,
    pub path: String,
    pub query: String,
    pub ordered_headers: Vec<(String, String)>,
    pub body: Vec<u8>,
    pub declaration_sha256: String,
    pub package_id: String,
    pub operation: String,
    pub write: bool,
}
#[derive(Clone, Debug)]
pub struct Declaration {
    value: Value,
    pub sha256: String,
    pub package_id: String,
}
fn string(v: &Value) -> Result<&str> {
    v.as_str().ok_or_else(|| refuse("declaration-invalid"))
}
fn number(v: &Value) -> Result<u64> {
    v.as_u64().ok_or_else(|| refuse("declaration-invalid"))
}
fn scalar(v: &Value) -> Result<String> {
    match v {
        Value::String(s) => Ok(s.clone()),
        Value::Number(_) | Value::Bool(_) => Ok(v.to_string()),
        _ => Err(refuse("binding-value-invalid")),
    }
}
// The contract hashes sorted JSON with Python-compatible number spelling and
// ensure_ascii string escaping. Write number tokens directly: reparsing them as
// Value would normalize away exponent sign/zero padding a second time.
fn canonical_bytes(value: &Value) -> Result<Vec<u8>> {
    fn quoted(value: &str, out: &mut String) -> Result<()> {
        let raw = serde_json::to_string(value).map_err(|_| refuse("declaration-invalid"))?;
        for c in raw.chars() {
            if (c as u32) >= 127 {
                let mut units = [0; 2];
                for unit in c.encode_utf16(&mut units).iter() {
                    out.push_str(&format!("\\u{unit:04x}"));
                }
            } else {
                out.push(c)
            }
        }
        Ok(())
    }
    fn write(value: &Value, out: &mut String) -> Result<()> {
        match value {
            Value::Null => out.push_str("null"),
            Value::Bool(b) => out.push_str(if *b { "true" } else { "false" }),
            Value::String(s) => quoted(s, out)?,
            Value::Array(values) => {
                out.push('[');
                for (i, v) in values.iter().enumerate() {
                    if i > 0 {
                        out.push(',')
                    }
                    write(v, out)?;
                }
                out.push(']');
            }
            Value::Object(values) => {
                out.push('{');
                let mut keys: Vec<_> = values.keys().collect();
                keys.sort();
                for (i, k) in keys.iter().enumerate() {
                    if i > 0 {
                        out.push(',')
                    }
                    quoted(k, out)?;
                    out.push(':');
                    write(&values[*k], out)?;
                }
                out.push('}');
            }
            Value::Number(n) => {
                let raw = n.to_string();
                if raw.contains(['.', 'e', 'E']) {
                    let f = n
                        .as_f64()
                        .filter(|f| f.is_finite())
                        .ok_or_else(|| refuse("declaration-number-invalid"))?;
                    let repr = format!("{f:?}");
                    if let Some((mantissa, exponent)) = repr.split_once('e') {
                        let exponent = exponent
                            .parse::<i32>()
                            .map_err(|_| refuse("declaration-number-invalid"))?;
                        out.push_str(&format!(
                            "{mantissa}e{}{:02}",
                            if exponent >= 0 { "+" } else { "-" },
                            exponent.abs()
                        ));
                    } else {
                        out.push_str(&repr)
                    }
                } else if raw == "-0" {
                    out.push('0')
                } else {
                    out.push_str(&raw)
                }
            }
        }
        Ok(())
    }
    let mut out = String::new();
    write(value, &mut out)?;
    Ok(out.into_bytes())
}
fn percent(s: &str) -> String {
    let mut out = String::new();
    for b in s.bytes() {
        if b.is_ascii_alphanumeric() || b"-._~".contains(&b) {
            out.push(b as char)
        } else {
            out.push_str(&format!("%{b:02X}"))
        }
    }
    out
}
fn relative(s: &str) -> Result<String> {
    if s.is_empty()
        || s.chars().any(|c| c.is_control() || "\\%?#".contains(c))
        || s.split('/').any(|p| matches!(p, "" | "." | ".."))
    {
        return Err(refuse("path-invalid"));
    }
    Ok(s.split('/').map(percent).collect::<Vec<_>>().join("/"))
}
fn path(parts: &Value, args: &Value) -> Result<String> {
    let mut out = String::new();
    for part in parts
        .as_array()
        .ok_or_else(|| refuse("declaration-invalid"))?
    {
        if let Some(s) = part.as_str() {
            out.push_str(s)
        } else {
            let value = scalar(
                args.get(string(&part["arg"])?)
                    .ok_or_else(|| refuse("input-schema"))?,
            )?;
            out.push_str(&match string(&part["encoding"])? {
                "path" => relative(&value)?,
                "segment" => {
                    if matches!(value.as_str(), "." | "..") || value.contains(['/', '\\']) {
                        return Err(refuse("path-invalid"));
                    }
                    percent(&value)
                }
                _ => return Err(refuse("binding-encoding-unsupported")),
            });
        }
    }
    Ok(out)
}
/// Resolve the closed data-binding vocabulary; no ambient host paths or identity.
pub fn resolve(x: &Value, args: &Value, context: &Value, results: &Value) -> Result<Value> {
    if let Some(o) = x.as_object() {
        if o.len() == 1 {
            if let Some(k) = o.get("arg") {
                return args
                    .get(string(k)?)
                    .cloned()
                    .ok_or_else(|| refuse("input-schema"));
            }
            if let Some(k) = o.get("cookie") {
                return results
                    .get("__mini_cookie_jar")
                    .and_then(|v| v.get(k.as_str()?))
                    .cloned()
                    .ok_or_else(|| refuse("app-cookie-missing"));
            }
            if let Some(k) = o.get("context") {
                return context
                    .get(string(k)?)
                    .cloned()
                    .ok_or_else(|| refuse("context-missing"));
            }
            if let Some(p) = o.get("result") {
                let mut v = results;
                for k in p.as_array().ok_or_else(|| refuse("declaration-invalid"))? {
                    v = if let Some(i) = k.as_u64() {
                        v.get(i as usize)
                    } else {
                        v.get(string(k)?)
                    }
                    .ok_or_else(|| refuse("result-binding-missing"))?;
                }
                return Ok(v.clone());
            }
            if let Some(a) = o.get("concat") {
                let mut s = String::new();
                for v in a.as_array().ok_or_else(|| refuse("declaration-invalid"))? {
                    s.push_str(&scalar(&resolve(v, args, context, results)?)?);
                }
                return Ok(json!(s));
            }
            if let Some(v) = o.get("jsonStringify") {
                return serde_json::to_string(&resolve(v, args, context, results)?)
                    .map(|s| json!(s))
                    .map_err(|_| refuse("binding-json-invalid"));
            }
            if let Some(v) = o.get("csv") {
                let rows = resolve(v, args, context, results)?;
                let mut out = String::new();
                for row in rows.as_array().ok_or_else(|| refuse("csv-input-invalid"))? {
                    let cells = row.as_array().ok_or_else(|| refuse("csv-input-invalid"))?;
                    for (i, cell) in cells.iter().enumerate() {
                        if i > 0 {
                            out.push(',')
                        }
                        let cell = cell.as_str().ok_or_else(|| refuse("csv-input-invalid"))?;
                        if cell.contains([',', '"', '\r', '\n'])
                            || (cell.is_empty() && cells.len() == 1)
                        {
                            out.push('"');
                            out.push_str(&cell.replace('"', "\"\""));
                            out.push('"')
                        } else {
                            out.push_str(cell)
                        }
                    }
                    out.push_str("\r\n");
                }
                return Ok(json!(out));
            }
            if let Some(v) = o.get("sha256") {
                return Ok(json!(format!(
                    "{:x}",
                    Sha256::digest(
                        resolve(v, args, context, results)?
                            .as_str()
                            .ok_or_else(|| refuse("hash-input-invalid"))?
                            .as_bytes()
                    )
                )));
            }
            // Path parts are an array; an object under `path` is an ordinary argument that is
            // named path (Davros qualification args are `{"path": ...}`).
            if let Some(p) = o.get("path").filter(|p| p.is_array()) {
                return Ok(json!(path(p, args)?));
            }
        }
        let mut out = serde_json::Map::new();
        for (k, v) in o {
            out.insert(k.clone(), resolve(v, args, context, results)?);
        }
        return Ok(Value::Object(out));
    }
    if let Some(a) = x.as_array() {
        return Ok(Value::Array(
            a.iter()
                .map(|v| resolve(v, args, context, results))
                .collect::<Result<_>>()?,
        ));
    }
    Ok(x.clone())
}
fn checked_alias(alias: &str) -> Result<()> {
    if alias.is_empty()
        || alias.len() > 32
        || !alias.as_bytes()[0].is_ascii_alphabetic()
        || !alias
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || b == b'_')
    {
        return Err(refuse("attachment-alias-invalid"));
    }
    Ok(())
}
pub fn bound_tool_name(alias: &str, operation: &str) -> Result<String> {
    checked_alias(alias)?;
    if operation == "qualify"
        || operation.is_empty()
        || operation.len() > 128
        || !operation.as_bytes()[0].is_ascii_alphabetic()
        || !operation
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || matches!(b, b'_' | b'.'))
        || operation.split('.').any(str::is_empty)
    {
        return Err(refuse("operation-name-invalid-or-reserved"));
    }
    Ok(format!(
        "mini_app_{}_{}",
        alias,
        operation.replace('.', "_")
    ))
}
pub fn qualification_tool_name(alias: &str) -> Result<String> {
    checked_alias(alias)?;
    Ok(format!("mini_app_{alias}_qualify"))
}
impl Declaration {
    pub fn load(bytes: &[u8]) -> Result<Self> {
        if bytes.len() > 4 * 1024 * 1024 {
            return Err(refuse("declaration-over-bound"));
        }
        let value: Value =
            serde_json::from_slice(bytes).map_err(|_| refuse("declaration-invalid"))?;
        if value["format"] != "mini-app-interface-v1" {
            return Err(refuse("interface-version-unsupported"));
        }
        let package_id = string(&value["packageId"])?.to_owned();
        if package_id.len() != 32
            || !package_id
                .bytes()
                .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
        {
            return Err(refuse("declaration-package-invalid"));
        }
        let ops = value["operations"]
            .as_object()
            .ok_or_else(|| refuse("declaration-invalid"))?;
        if ops.is_empty() {
            return Err(refuse("declaration-invalid"));
        }
        for key in ["bodyBytes", "replyBytes"] {
            if !(1..=67108864).contains(&number(&value["limits"][key])?) {
                return Err(refuse("declaration-limit-invalid"));
            }
        }
        let mut names = std::collections::BTreeSet::new();
        for name in ops.keys() {
            if !names.insert(bound_tool_name("bound", name)?) {
                return Err(refuse("operation-tool-name-collision"));
            }
        }
        for op in ops.values() {
            if !op["input"].is_object() || !op["output"].is_object() || !op["write"].is_boolean() {
                return Err(refuse("declaration-invalid"));
            }
        }
        for op in ops.values() {
            transport::validate_binding(&op["binding"])?;
            check_schema(&op["input"], 0)?;
            check_schema(&op["output"], 0)?;
        }
        if let Some(defs) = value["$defs"].as_object() {
            for schema in defs.values() {
                check_schema(schema, 0)?;
            }
        }
        if let Some(steps) = value["qualification"].as_array() {
            for step in steps {
                if let Some(wait) = step.get("await") {
                    if ops
                        .get(string(&step["op"])?)
                        .is_none_or(|op| op["write"] != false)
                    {
                        return Err(refuse("declaration-mutating-await"));
                    }
                    await_bounds(wait)?;
                }
            }
        }
        let sha256 = format!("{:x}", Sha256::digest(canonical_bytes(&value)?));
        let d = Self {
            value,
            sha256,
            package_id,
        };
        for name in ops_keys(&d.value)? {
            d.dependencies(&name, &mut Vec::new())?;
        }
        Ok(d)
    }
    fn dependencies(&self, name: &str, stack: &mut Vec<String>) -> Result<()> {
        if stack.iter().any(|n| n == name) {
            return Err(refuse("declaration-cyclic-relation"));
        }
        if stack.len() > 64 {
            return Err(refuse("declaration-dependency-over-bound"));
        }
        let op = self.operation(name)?;
        stack.push(name.into());
        if let Some(reqs) = op.get("requires") {
            for req in reqs
                .as_array()
                .ok_or_else(|| refuse("declaration-invalid"))?
            {
                let n = string(&req["op"])?;
                if self.operation(n)?["write"] != false {
                    return Err(refuse("declaration-mutating-relation"));
                }
                self.dependencies(n, stack)?;
            }
        }
        if let Some(steps) = op.get("prepare") {
            let mut ids = std::collections::BTreeSet::new();
            for step in steps
                .as_array()
                .ok_or_else(|| refuse("declaration-invalid"))?
            {
                let id = string(&step["id"])?;
                if !ids.insert(id) {
                    return Err(refuse("declaration-preparation-id"));
                }
                let n = string(&step["op"])?;
                if self.operation(n)?["write"] != false {
                    return Err(refuse("declaration-mutating-preparation"));
                }
                self.dependencies(n, stack)?;
            }
        }
        stack.pop();
        Ok(())
    }
    fn operation(&self, name: &str) -> Result<&Value> {
        self.value["operations"]
            .get(name)
            .ok_or_else(|| refuse("operation-unknown"))
    }
    pub fn tools(&self) -> Result<Vec<Value>> {
        let mut tools = vec![];
        for (name, op) in self.value["operations"].as_object().unwrap() {
            if op["internal"] == true {
                continue;
            }
            let mut input = op["input"].clone();
            input["$defs"] = self.value["$defs"].clone();
            tools.push(json!({"name":format!("mini_{}_{}",string(&self.value["name"])?,name.replace('.',"_")),"description":op["description"],"inputSchema":input,"outputSchema":{"type":"object","properties":{"value":op["output"]},"required":["value"],"additionalProperties":false,"$defs":self.value["$defs"]},"operation":name,"packageId":self.package_id,"interfaceSha256":self.sha256,"annotations":{"readOnlyHint":op["write"]==false,"idempotentHint":false},"_meta":{"interfaceDigest":self.sha256,"packageId":self.package_id,"operation":name}}));
        }
        Ok(tools)
    }
    pub fn bound_tools(&self, alias: &str) -> Result<Vec<Value>> {
        checked_alias(alias)?;
        let mut tools = self.tools()?;
        for tool in &mut tools {
            let op = string(&tool["operation"])?;
            tool["name"] = json!(bound_tool_name(alias, op)?);
            tool["_meta"]["attachment"] = json!(alias);
        }
        Ok(tools)
    }
    pub fn validate_input(&self, name: &str, args: &Value) -> Result<()> {
        self.validate(&self.operation(name)?["input"], args, "input", 0)
    }
    pub fn prepare(&self, name: &str, args: &Value, context: &Value) -> Result<PreparedCall> {
        let op = self.operation(name)?;
        self.validate(&op["input"], args, "input", 0)?;
        if op
            .get("prepare")
            .and_then(Value::as_array)
            .is_some_and(|a| !a.is_empty())
        {
            return Err(refuse("preparation-required"));
        }
        if op
            .get("requires")
            .and_then(Value::as_array)
            .is_some_and(|a| !a.is_empty())
        {
            return Err(refuse("relation-preflight-required"));
        }
        self.encode(name, args, context)
    }
    fn encode(&self, name: &str, args: &Value, context: &Value) -> Result<PreparedCall> {
        self.encode_results(name, args, context, &Value::Null)
    }
    fn encode_results(
        &self,
        name: &str,
        args: &Value,
        context: &Value,
        results: &Value,
    ) -> Result<PreparedCall> {
        let op = self.operation(name)?;
        self.encode_http_binding(
            name,
            &op["binding"],
            op["write"] == true,
            args,
            context,
            results,
        )
    }
    fn encode_http_binding(
        &self,
        name: &str,
        b: &Value,
        write: bool,
        args: &Value,
        context: &Value,
        results: &Value,
    ) -> Result<PreparedCall> {
        if b["protocol"] != "http" {
            return Err(refuse("transport-unsupported"));
        }
        let empty = json!({});
        let mut headers = resolve(b.get("headers").unwrap_or(&empty), args, context, results)?;
        let count = ["json", "base64", "text", "form", "multipart"]
            .iter()
            .filter(|k| b.get(**k).is_some())
            .count();
        if count > 1 {
            return Err(refuse("declaration-ambiguous-body"));
        }
        let body = if let Some(v) = b.get("json") {
            headers["content-type"] = json!("application/json");
            serde_json::to_vec(&resolve(v, args, context, results)?)
                .map_err(|_| refuse("binding-json"))?
        } else if let Some(v) = b.get("base64") {
            binary(&resolve(v, args, context, results)?)?
        } else if let Some(v) = b.get("form") {
            headers["content-type"] = json!("application/x-www-form-urlencoded");
            let fields = resolve(v, args, context, results)?;
            fields
                .as_object()
                .ok_or_else(|| refuse("binding-form-invalid"))?
                .iter()
                .map(|(k, v)| Ok(format!("{}={}", percent(k), percent(&scalar(v)?))))
                .collect::<Result<Vec<_>>>()?
                .join("&")
                .into_bytes()
        } else if let Some(parts) = b.get("multipart") {
            let boundary = format!("mini{}", &self.sha256[..32]);
            headers["content-type"] = json!(format!("multipart/form-data; boundary={boundary}"));
            let mut body = vec![];
            for part in parts
                .as_array()
                .ok_or_else(|| refuse("binding-multipart-invalid"))?
            {
                let name = multipart_token(string(&part["name"])?)?;
                let filename = part
                    .get("filename")
                    .map(|v| resolve(v, args, context, results).and_then(|v| scalar(&v)))
                    .transpose()?;
                let mut disposition =
                    format!("--{boundary}\r\nContent-Disposition: form-data; name=\"{name}\"");
                if let Some(f) = filename {
                    disposition.push_str(&format!("; filename=\"{}\"", multipart_token(&f)?));
                }
                disposition.push_str("\r\n");
                if let Some(t) = part.get("contentType") {
                    let t = scalar(&resolve(t, args, context, results)?)?;
                    if t.chars().any(|c| c.is_control()) {
                        return Err(refuse("header-invalid"));
                    }
                    disposition.push_str(&format!("Content-Type: {t}\r\n"));
                }
                disposition.push_str("\r\n");
                body.extend_from_slice(disposition.as_bytes());
                let bytes = match (part.get("text"), part.get("base64")) {
                    (Some(v), None) => scalar(&resolve(v, args, context, results)?)?.into_bytes(),
                    (None, Some(v)) => binary(&resolve(v, args, context, results)?)?,
                    _ => return Err(refuse("binding-multipart-invalid")),
                };
                if bytes
                    .windows(boundary.len())
                    .any(|w| w == boundary.as_bytes())
                {
                    return Err(refuse("multipart-boundary-collision"));
                }
                body.extend(bytes);
                body.extend_from_slice(b"\r\n");
            }
            body.extend_from_slice(format!("--{boundary}--\r\n").as_bytes());
            body
        } else if let Some(v) = b.get("text") {
            scalar(&resolve(v, args, context, results)?)?.into_bytes()
        } else {
            vec![]
        };
        if body.len() as u64 > number(&self.value["limits"]["bodyBytes"])? {
            return Err(refuse("body-over-bound"));
        }
        if let Some(cookies) = b.get("cookies") {
            if headers
                .as_object()
                .is_none_or(|o| o.keys().any(|k| k.eq_ignore_ascii_case("cookie")))
            {
                return Err(refuse("cookie-binding-ambiguous"));
            }
            let cookies = resolve(cookies, args, context, results)?;
            let mut pairs = vec![];
            for (k, v) in cookies
                .as_object()
                .ok_or_else(|| refuse("app-cookie-invalid"))?
            {
                if k == "__Host-mini_spk_session" {
                    return Err(refuse("app-cookie-reserved"));
                }
                let v = string(v)?;
                if k.is_empty()
                    || k.chars()
                        .any(|c| !c.is_ascii_alphanumeric() && !"_-.".contains(c))
                    || v.chars().any(|c| c.is_control() || c == ';')
                {
                    return Err(refuse("app-cookie-invalid"));
                }
                pairs.push(format!("{k}={v}"));
            }
            if !pairs.is_empty() {
                headers["cookie"] = json!(pairs.join("; "));
            }
        }
        let mut ordered_headers = vec![];
        for (k, v) in headers
            .as_object()
            .ok_or_else(|| refuse("header-invalid"))?
        {
            let s = string(v)?;
            if k.is_empty()
                || k.chars().any(|c| !c.is_ascii_alphanumeric() && c != '-')
                || s.chars().any(|c| c.is_control())
            {
                return Err(refuse("header-invalid"));
            }
            let lower = k.to_ascii_lowercase();
            if lower.starts_with("x-sandstorm-")
                || matches!(lower.as_str(), "host" | "authorization")
            {
                return Err(refuse("header-identity-forbidden"));
            }
            if lower == "cookie"
                && s.split(';').any(|p| {
                    p.trim()
                        .split_once('=')
                        .is_some_and(|(k, _)| k == "__Host-mini_spk_session")
                })
            {
                return Err(refuse("app-cookie-reserved"));
            }
            ordered_headers.push((k.clone(), s.into()));
        }
        let q = resolve(b.get("query").unwrap_or(&empty), args, context, results)?;
        let mut query = vec![];
        for (k, v) in q.as_object().ok_or_else(|| refuse("query-invalid"))? {
            query.push(format!("{}={}", percent(k), percent(&scalar(v)?)))
        }
        Ok(PreparedCall {
            method: string(&b["method"])?.into(),
            path: path(&b["path"], args)?,
            query: query.join("&"),
            ordered_headers,
            body,
            declaration_sha256: self.sha256.clone(),
            package_id: self.package_id.clone(),
            operation: name.into(),
            write,
        })
    }
    pub fn decode(
        &self,
        p: &PreparedCall,
        status: u16,
        headers: &[(String, String)],
        body: &[u8],
    ) -> Result<Value> {
        self.decode_for(p, &json!({}), &json!({}), status, headers, body)
    }
    pub fn decode_for(
        &self,
        p: &PreparedCall,
        args: &Value,
        context: &Value,
        status: u16,
        headers: &[(String, String)],
        body: &[u8],
    ) -> Result<Value> {
        self.decode_results(p, args, context, &Value::Null, status, headers, body)
    }
    fn decode_results(
        &self,
        p: &PreparedCall,
        args: &Value,
        context: &Value,
        results: &Value,
        status: u16,
        headers: &[(String, String)],
        body: &[u8],
    ) -> Result<Value> {
        let op = self.operation(&p.operation)?;
        let write = op["write"] == true;
        (|| {
            let value = self.decode_inner(p, status, headers, body)?;
            let value = project(op, value, args, context, results)?;
            self.validate(&op["output"], &value, "output", 0)?;
            Ok(value)
        })()
        .map_err(|mut e: Refusal| {
            if write
                && op["binding"]["status"]
                    .as_array()
                    .is_some_and(|a| a.contains(&json!(status)))
            {
                e.uncertain = true;
            }
            e
        })
    }
    fn decode_inner(
        &self,
        p: &PreparedCall,
        status: u16,
        headers: &[(String, String)],
        body: &[u8],
    ) -> Result<Value> {
        if p.declaration_sha256 != self.sha256 || p.package_id != self.package_id {
            return Err(refuse("interface-binding-mismatch"));
        }
        let op = self.operation(&p.operation)?;
        self.decode_http_binding(op, status, headers, body)
    }
    fn decode_http_binding(
        &self,
        op: &Value,
        status: u16,
        headers: &[(String, String)],
        body: &[u8],
    ) -> Result<Value> {
        let write = op["write"] == true;
        if body.len() as u64 > number(&self.value["limits"]["replyBytes"])? {
            return Err(Refusal {
                name: "reply-over-bound".into(),
                uncertain: write,
            });
        }
        if !op["binding"]["status"]
            .as_array()
            .ok_or_else(|| refuse("declaration-invalid"))?
            .contains(&json!(status))
        {
            return Err(Refusal {
                name: match status {
                    401 => "app-auth-required",
                    403 => "app-permission-denied",
                    404 => "app-not-found",
                    409 => "app-conflict",
                    412 => "app-precondition-failed",
                    500..=599 if write => "app-server-error-after-dispatch",
                    _ => "app-http-status",
                }
                .into(),
                uncertain: write && status >= 500,
            });
        }
        let value = match string(&op["binding"]["decode"])? {
            "json" => {
                if !headers.iter().any(|(k, v)| {
                    let mime = v
                        .split(';')
                        .next()
                        .unwrap_or("")
                        .trim()
                        .to_ascii_lowercase();
                    k.eq_ignore_ascii_case("content-type")
                        && (mime.contains("json")
                            || op["binding"]["acceptedContentTypes"]
                                .as_array()
                                .is_some_and(|a| {
                                    a.iter().any(|t| t.as_str() == Some(mime.as_str()))
                                }))
                }) {
                    return Err(refuse("app-content-type"));
                }
                if body.is_empty() {
                    op["binding"]
                        .get("emptyValue")
                        .cloned()
                        .ok_or_else(|| refuse("app-response-invalid"))?
                } else {
                    serde_json::from_slice(body).map_err(|_| refuse("app-response-invalid"))?
                }
            }
            "json-string-fragment" => {
                if op["internal"] != true || write {
                    return Err(refuse("binding-auth-fragment-invalid"));
                }
                let prefix = string(&op["binding"]["fragment"]["prefix"])?;
                let suffix = string(&op["binding"]["fragment"]["suffix"])?;
                if !(1..=256).contains(&prefix.chars().count())
                    || !(1..=64).contains(&suffix.chars().count())
                {
                    return Err(refuse("binding-auth-fragment-invalid"));
                }
                let text =
                    std::str::from_utf8(body).map_err(|_| refuse("app-auth-fragment-invalid"))?;
                if text.matches(prefix).count() != 1 {
                    return Err(refuse("app-auth-fragment-invalid"));
                }
                let fragment = text.split_once(prefix).unwrap().1;
                if !fragment.starts_with('"') {
                    return Err(refuse("app-auth-fragment-invalid"));
                }
                let mut stream = serde_json::Deserializer::from_str(fragment).into_iter::<Value>();
                let value = stream
                    .next()
                    .transpose()
                    .map_err(|_| refuse("app-auth-fragment-invalid"))?
                    .filter(Value::is_string)
                    .ok_or_else(|| refuse("app-auth-fragment-invalid"))?;
                if !fragment[stream.byte_offset()..]
                    .trim_start()
                    .starts_with(suffix)
                {
                    return Err(refuse("app-auth-fragment-invalid"));
                }
                value
            }
            "json-lines" => {
                let text = std::str::from_utf8(body).map_err(|_| refuse("app-text-invalid"))?;
                let rows = text
                    .lines()
                    .filter(|s| !s.trim().is_empty())
                    .map(|line| {
                        serde_json::from_str::<Value>(line)
                            .map_err(|_| refuse("app-response-invalid"))
                    })
                    .collect::<Result<Vec<_>>>()?;
                json!(rows)
            }
            "text" => json!(std::str::from_utf8(body).map_err(|_| refuse("app-text-invalid"))?),
            "base64" => json!({"contentBase64":STANDARD.encode(body)}),
            "status" => json!({"status":status}),
            "rss" => rss(
                body,
                number(&self.value["limits"]["snapshotDocuments"])? as usize,
            )?,
            "dav-multistatus" => dav(body, false)?,
            "caldav-multistatus" => dav(body, true)?,
            _ => return Err(refuse("binding-decoding-unsupported")),
        };
        if let Some(mapping) = op["binding"].get("responseHeaders") {
            let mut out = serde_json::Map::new();
            for (field, name) in mapping
                .as_object()
                .ok_or_else(|| refuse("binding-response-headers-invalid"))?
            {
                let name = string(name)?;
                if !matches!(
                    name,
                    "etag"
                        | "last-modified"
                        | "content-type"
                        | "content-length"
                        | "x-sandstorm-app-data-version"
                ) {
                    return Err(refuse("binding-response-headers-invalid"));
                }
                let found: Vec<_> = headers
                    .iter()
                    .filter(|(k, _)| k.eq_ignore_ascii_case(name))
                    .collect();
                if found.len() != 1 {
                    return Err(refuse("app-response-header-missing-or-duplicate"));
                }
                let value = &found[0].1;
                if value.len() > 4096 || value.chars().any(char::is_control) {
                    return Err(refuse("app-response-header-invalid"));
                }
                out.insert(field.clone(), json!(value));
            }
            return Ok(json!({"body":value,"headers":out}));
        }
        Ok(value)
    }
    fn validate(&self, s: &Value, v: &Value, phase: &str, depth: usize) -> Result<()> {
        let bad = || refuse(&format!("{phase}-schema"));
        if depth > 64 {
            return Err(bad());
        }
        for key in ["oneOf", "anyOf", "allOf"] {
            if let Some(choices) = s.get(key) {
                let choices = choices.as_array().ok_or_else(bad)?;
                let count = choices
                    .iter()
                    .filter(|sub| self.validate(sub, v, phase, depth + 1).is_ok())
                    .count();
                if match key {
                    "oneOf" => count != 1,
                    "anyOf" => count == 0,
                    _ => count != choices.len(),
                } {
                    return Err(bad());
                }
            }
        }
        if let Some(r) = s.get("$ref") {
            let name = string(r)?.strip_prefix("#/$defs/").ok_or_else(bad)?;
            return self.validate(
                self.value["$defs"].get(name).ok_or_else(bad)?,
                v,
                phase,
                depth + 1,
            );
        }
        if let Some(t) = s.get("type") {
            let types: Vec<&str> = if let Some(a) = t.as_array() {
                a.iter().map(string).collect::<Result<_>>()?
            } else {
                vec![string(t)?]
            };
            if !types.iter().any(|t| match *t {
                "object" => v.is_object(),
                "array" => v.is_array(),
                "string" => v.is_string(),
                "integer" => v.as_i64().is_some() || v.as_u64().is_some(),
                "number" => v.is_number(),
                "boolean" => v.is_boolean(),
                "null" => v.is_null(),
                _ => false,
            }) {
                return Err(bad());
            }
        }
        if let Some(a) = s.get("enum") {
            if !a.as_array().ok_or_else(bad)?.contains(v) {
                return Err(bad());
            }
        }
        if let Some(c) = s.get("const") {
            if c != v {
                return Err(bad());
            }
        }
        if let Some(o) = v.as_object() {
            if s["maxProperties"]
                .as_u64()
                .is_some_and(|n| o.len() as u64 > n)
                || s["minProperties"]
                    .as_u64()
                    .is_some_and(|n| (o.len() as u64) < n)
            {
                return Err(bad());
            }
            if let Some(required) = s["required"].as_array() {
                for k in required {
                    if !o.contains_key(string(k)?) {
                        return Err(bad());
                    }
                }
            }
            for (k, x) in o {
                if let Some(sub) = s["properties"].get(k) {
                    self.validate(sub, x, phase, depth + 1)?
                } else if s["additionalProperties"] == false {
                    return Err(bad());
                } else if s["additionalProperties"].is_object() {
                    self.validate(&s["additionalProperties"], x, phase, depth + 1)?;
                }
            }
        }
        if let Some(a) = v.as_array() {
            if s["maxItems"].as_u64().is_some_and(|n| a.len() as u64 > n)
                || s["minItems"].as_u64().is_some_and(|n| (a.len() as u64) < n)
            {
                return Err(bad());
            }
            if let Some(key) = s["uniqueBy"].as_str() {
                let bad = || refuse(&format!("{phase}-unique-key"));
                if a.len() > 1000 {
                    return Err(bad());
                }
                let mut seen = std::collections::BTreeSet::new();
                for item in a {
                    let v = item.as_object().and_then(|o| o.get(key)).ok_or_else(bad)?;
                    let key = if let Some(s) = v.as_str() {
                        format!("s:{s}")
                    } else if v.as_i64().is_some() || v.as_u64().is_some() {
                        format!("i:{v}")
                    } else {
                        return Err(bad());
                    };
                    if !seen.insert(key) {
                        return Err(bad());
                    }
                }
            }
            if let Some(sub) = s.get("items") {
                for x in a {
                    self.validate(sub, x, phase, depth + 1)?
                }
            }
        }
        if let Some(text) = v.as_str() {
            let n = text.chars().count() as u64;
            if s["maxLength"].as_u64().is_some_and(|m| n > m)
                || s["minLength"].as_u64().is_some_and(|m| n < m)
            {
                return Err(bad());
            }
            if let Some(pat) = s["pattern"].as_str() {
                if !regex_lite::Regex::new(pat)
                    .map_err(|_| refuse("schema-pattern-unsupported"))?
                    .is_match(text)
                {
                    return Err(bad());
                }
            }
            if s["format"] == "relative-path" {
                relative(text)?;
            }
            if s["contentEncoding"] == "base64" {
                let bytes = binary(v)?;
                let limit = if phase == "input" {
                    "bodyBytes"
                } else {
                    "replyBytes"
                };
                if bytes.len() as u64 > number(&self.value["limits"][limit])? {
                    return Err(refuse(if phase == "input" {
                        "body-over-bound"
                    } else {
                        "reply-over-bound"
                    }));
                }
            }
        }
        if let Some(n) = v.as_f64() {
            if s["minimum"].as_f64().is_some_and(|m| n < m)
                || s["maximum"].as_f64().is_some_and(|m| n > m)
                || s["exclusiveMinimum"].as_f64().is_some_and(|m| n <= m)
                || s["exclusiveMaximum"].as_f64().is_some_and(|m| n >= m)
            {
                return Err(bad());
            }
        }
        Ok(())
    }
}
fn ops_keys(v: &Value) -> Result<Vec<String>> {
    Ok(v["operations"]
        .as_object()
        .ok_or_else(|| refuse("declaration-invalid"))?
        .keys()
        .cloned()
        .collect())
}
fn binary(v: &Value) -> Result<Vec<u8>> {
    let s = string(v)?;
    let bytes = STANDARD.decode(s).map_err(|_| refuse("binary-encoding"))?;
    if STANDARD.encode(&bytes) != s {
        return Err(refuse("binary-encoding"));
    }
    Ok(bytes)
}
fn dav(body: &[u8], caldav: bool) -> Result<Value> {
    let text = std::str::from_utf8(body).map_err(|_| refuse("dav-response-invalid"))?;
    let upper = text.to_ascii_uppercase();
    if text.contains('\0') || upper.contains("<!DOCTYPE") || upper.contains("<!ENTITY") {
        return Err(refuse("dav-xml-unsafe"));
    }
    let doc = roxmltree::Document::parse(text).map_err(|_| refuse("dav-response-invalid"))?;
    let tag = |n: roxmltree::Node<'_, '_>, name: &str| n.has_tag_name(("DAV:", name));
    let root = doc.root_element();
    if !tag(root, "multistatus") {
        return Err(refuse("dav-response-invalid"));
    }
    let mut out = vec![];
    for r in root.children().filter(|n| tag(*n, "response")) {
        let href = r
            .children()
            .find(|n| tag(*n, "href"))
            .and_then(|n| n.text())
            .ok_or_else(|| refuse("dav-response-invalid"))?;
        let mut collection = None;
        let mut size = Value::Null;
        let mut etag = Value::Null;
        let mut calendar_data = None;
        for ps in r.children().filter(|n| tag(*n, "propstat")) {
            let status = ps
                .children()
                .find(|n| tag(*n, "status"))
                .and_then(|n| n.text())
                .ok_or_else(|| refuse("dav-response-invalid"))?;
            if !status.starts_with("HTTP/") {
                return Err(refuse("dav-response-invalid"));
            }
            let code = status
                .split_whitespace()
                .nth(1)
                .and_then(|s| s.parse::<u16>().ok())
                .ok_or_else(|| refuse("dav-response-invalid"))?;
            if code == 404 {
                continue;
            }
            if !(200..300).contains(&code) {
                return Err(refuse("dav-property-refused"));
            }
            let props = ps
                .children()
                .find(|n| tag(*n, "prop"))
                .ok_or_else(|| refuse("dav-response-invalid"))?;
            for p in props.children().filter(|n| n.is_element()) {
                if tag(p, "resourcetype") {
                    collection = Some(p.children().any(|n| tag(n, "collection")))
                } else if tag(p, "getcontentlength") {
                    size = match p.text() {
                        None => Value::Null,
                        Some(t) => json!(t
                            .parse::<u64>()
                            .map_err(|_| refuse("dav-response-invalid"))?),
                    };
                } else if p.has_tag_name(("urn:ietf:params:xml:ns:caldav", "calendar-data")) {
                    calendar_data = Some(p.text().unwrap_or("").to_owned());
                } else if tag(p, "getetag") {
                    etag = p.text().map(|t| json!(t)).unwrap_or(Value::Null)
                }
            }
        }
        if caldav {
            if !etag.is_string() {
                return Err(refuse("caldav-property-missing"));
            }
            out.push(json!({"href":href,"etag":etag,"calendarData":calendar_data.ok_or_else(||refuse("caldav-property-missing"))?}));
        } else {
            out.push(json!({"href":href,"collection":collection.ok_or_else(||refuse("dav-property-missing"))?,"bytes":size,"etag":etag}));
        }
    }
    Ok(json!(out))
}

fn multipart_token(s: &str) -> Result<String> {
    if s.is_empty() || s.chars().any(|c| c.is_control() || matches!(c, '"' | '\\')) {
        return Err(refuse("binding-multipart-invalid"));
    }
    Ok(s.into())
}

/// Selected by the controller from its authenticated attachment, never tool arguments.
/// The admission callback must recheck this same subject/session on EVERY send.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SessionBinding {
    pub package_id: String,
    pub subject: String,
    pub app: String,
    pub generation: String,
    pub session: String,
    pub session_generation: String,
}
/// A definite response from the existing admitted application API. `receipt` is
/// retained verbatim; typed projections never replace native completion evidence.
#[derive(Clone, Debug)]
pub struct NativeReply {
    pub status: u16,
    pub headers: Vec<(String, String)>,
    pub body: Vec<u8>,
    pub receipt: Value,
}
#[derive(Debug)]
pub struct Execution {
    pub outcome: Result<Value>,
    pub receipts: Vec<Value>,
}
impl Declaration {
    /// Run reads/preparations and exactly one requested operation, without retries.
    /// `dispatch` is the existing current-authority admission/physical-custody path.
    /// Its errors distinguish no-send refusals from uncertain sends. All definite
    /// native receipts survive even if response decoding or later preflight fails.
    pub fn execute<F>(
        &self,
        name: &str,
        args: &Value,
        context: &Value,
        binding: &SessionBinding,
        mut dispatch: F,
    ) -> Execution
    where
        F: FnMut(&SessionBinding, &PreparedCall) -> Result<NativeReply>,
    {
        let mut receipts = vec![];
        let outcome = if binding.package_id != self.package_id {
            Err(refuse("package-binding-mismatch"))
        } else {
            self.execute_inner(
                name,
                args,
                context,
                binding,
                &mut dispatch,
                &mut receipts,
                &mut CookieJar::default(),
                0,
            )
        };
        Execution { outcome, receipts }
    }
    fn execute_inner<F>(
        &self,
        name: &str,
        args: &Value,
        context: &Value,
        binding: &SessionBinding,
        dispatch: &mut F,
        receipts: &mut Vec<Value>,
        cookies: &mut CookieJar,
        depth: usize,
    ) -> Result<Value>
    where
        F: FnMut(&SessionBinding, &PreparedCall) -> Result<NativeReply>,
    {
        if depth > 32 {
            return Err(refuse("preparation-depth-over-bound"));
        }
        let op = self.operation(name)?;
        self.validate(&op["input"], args, "input", 0)?;
        let mut context = context.clone();
        if let Some(ms) = context["nowMs"].as_u64() {
            context["nowIso"] = json!(utc_iso(ms)?);
        }
        let context = &context;
        let mut results = json!({});
        if let Some(steps) = op.get("prepare") {
            for step in steps
                .as_array()
                .ok_or_else(|| refuse("declaration-invalid"))?
            {
                let subname = string(&step["op"])?;
                if self.operation(subname)?["write"] != false {
                    return Err(refuse("declaration-mutating-preparation"));
                }
                let subargs = resolve(&step["args"], args, context, &results)?;
                let value = self.execute_inner(
                    subname,
                    &subargs,
                    context,
                    binding,
                    dispatch,
                    receipts,
                    cookies,
                    depth + 1,
                )?;
                let id = string(&step["id"])?;
                if results.get(id).is_some() {
                    return Err(refuse("declaration-preparation-id"));
                }
                results[id] = value;
            }
        }
        if let Some(reqs) = op.get("requires") {
            for req in reqs
                .as_array()
                .ok_or_else(|| refuse("declaration-invalid"))?
            {
                let subname = string(&req["op"])?;
                if self.operation(subname)?["write"] != false {
                    return Err(refuse("declaration-mutating-relation"));
                }
                let subargs = resolve(&req["args"], args, context, &results)?;
                let value = self.execute_inner(
                    subname,
                    &subargs,
                    context,
                    binding,
                    dispatch,
                    receipts,
                    cookies,
                    depth + 1,
                )?;
                if let Some(exists) = req.get("exists") {
                    for check in exists
                        .as_array()
                        .ok_or_else(|| refuse("declaration-invalid"))?
                    {
                        let collection = string(&check["collection"])?;
                        let expected = resolve(&check["where"], args, context, &results)?;
                        let rows = value[collection]
                            .as_array()
                            .ok_or_else(|| refuse("relation-not-visible-or-mismatched"))?;
                        if rows.iter().filter(|v| matches_fields(v, &expected)).count() != 1 {
                            return Err(refuse("relation-not-visible-or-mismatched"));
                        }
                    }
                }
                if let Some(checks) = req.get("assert") {
                    for check in checks
                        .as_array()
                        .ok_or_else(|| refuse("declaration-invalid"))?
                    {
                        let got = lookup(&value, &check["path"])?;
                        if *got != resolve(&check["equals"], args, context, &results)? {
                            return Err(refuse("precondition-failed"));
                        }
                    }
                }
            }
        }
        let target = if op["binding"]["protocol"] == "http" {
            path(&op["binding"]["path"], args)?
        } else {
            String::new()
        };
        let scoped = cookies.for_path(&target)?;
        results["__mini_cookie_jar"] = json!(scoped);
        if op["binding"]["protocol"] == "conversation" {
            let value = self
                .execute_conversation(name, args, context, binding, dispatch, receipts, cookies)?;
            return (|| {
                let value = project(op, value, args, context, &results)?;
                self.validate(&op["output"], &value, "output", 0)?;
                Ok(value)
            })()
            .map_err(|mut e: Refusal| {
                e.uncertain |= op["write"] == true;
                e
            });
        }
        if op["binding"]["protocol"] == "ddp" {
            let value = self.execute_ddp(name, args, context, binding, dispatch, receipts)?;
            return (|| {
                let value = project(op, value, args, context, &results)?;
                self.validate(&op["output"], &value, "output", 0)?;
                Ok(value)
            })()
            .map_err(|mut e: Refusal| {
                e.uncertain |= op["write"] == true;
                e
            });
        }
        let mut call = self.encode_results(name, args, context, &results)?;
        if self.value["auth"]["appCookies"] == "retain" && !scoped.is_empty() {
            if call
                .ordered_headers
                .iter()
                .any(|(k, _)| k.eq_ignore_ascii_case("cookie"))
            {
                return Err(refuse("cookie-binding-ambiguous"));
            }
            call.ordered_headers.push((
                "cookie".into(),
                scoped
                    .iter()
                    .map(|(k, v)| format!("{k}={v}"))
                    .collect::<Vec<_>>()
                    .join("; "),
            ));
        }
        let reply = dispatch(binding, &call)?;
        receipts.push(reply.receipt.clone());
        let value = self
            .decode_results(
                &call,
                args,
                context,
                &results,
                reply.status,
                &reply.headers,
                &reply.body,
            )
            .map_err(|mut e: Refusal| {
                if call.write
                    && matches!(
                        e.name.as_str(),
                        "output-schema"
                            | "app-response-invalid"
                            | "app-content-type"
                            | "app-text-invalid"
                            | "reply-over-bound"
                            | "dav-response-invalid"
                    )
                {
                    e.uncertain = true;
                }
                e
            })?;
        if self.value["auth"]["appCookies"] == "retain" {
            cookies
                .retain(&reply.headers, &call.path)
                .map_err(|mut e: Refusal| {
                    e.uncertain |= call.write;
                    e
                })?;
        }
        Ok(value)
    }
    /// Qualification uses this executor too; each step has fresh current admission.
    pub fn qualify<F>(
        &self,
        context: &Value,
        binding: &SessionBinding,
        mut dispatch: F,
    ) -> Execution
    where
        F: FnMut(&SessionBinding, &PreparedCall) -> Result<NativeReply>,
    {
        let mut receipts = vec![];
        let mut results = json!({});
        let outcome = (|| {
            if binding.package_id != self.package_id {
                return Err(refuse("package-binding-mismatch"));
            }
            let steps = self.value["qualification"]
                .as_array()
                .ok_or_else(|| refuse("declaration-invalid"))?;
            let mut saw_write = false;
            let mut readback = false;
            for step in steps {
                let op = self.operation(string(&step["op"])?)?;
                if op["write"] == true {
                    if step["assert"].as_array().is_some_and(|a| !a.is_empty())
                        && compound_readback(op)
                    {
                        readback = true;
                    }
                    saw_write = true
                } else if saw_write && step["assert"].as_array().is_some_and(|a| !a.is_empty()) {
                    readback = true
                }
            }
            if !readback {
                return Err(refuse("qualification-write-readback-absent"));
            }
            for step in steps {
                let name = string(&step["op"])?;
                let args = resolve(&step["args"], &json!({}), context, &results)?;
                let (attempts, interval, retry) = if let Some(wait) = step.get("await") {
                    if self.operation(name)?["write"] != false {
                        return Err(refuse("declaration-mutating-await"));
                    }
                    await_bounds(wait)?
                } else {
                    (1, 0.0, vec![])
                };
                for attempt in 0..attempts {
                    let mut status = None;
                    let value = self.execute_inner(
                        name,
                        &args,
                        context,
                        binding,
                        &mut |b, p| {
                            let reply = dispatch(b, p)?;
                            status = Some(reply.status);
                            Ok(reply)
                        },
                        &mut receipts,
                        &mut CookieJar::default(),
                        0,
                    );
                    let checked = value.and_then(|value| {
                        results[string(&step["id"])?] = value.clone();
                        scenario_assertions(&value, step.get("assert"), context, &results)?;
                        Ok(value)
                    });
                    match checked {
                        Ok(_) => break,
                        Err(e) => {
                            let retryable = !e.uncertain
                                && (e.name == "readback-mismatch"
                                    || (e.name == "app-http-status"
                                        && status.is_some_and(|s| retry.contains(&s))));
                            if !retryable || attempt + 1 == attempts {
                                return Err(e);
                            }
                            if interval > 0.0 {
                                #[cfg(not(target_arch = "wasm32"))]
                                std::thread::sleep(std::time::Duration::from_secs_f64(interval));
                                #[cfg(target_arch = "wasm32")]
                                return Err(refuse("qualification-native-required"));
                            }
                        }
                    }
                }
            }
            Ok(results)
        })();
        Execution { outcome, receipts }
    }
}
fn matches_fields(value: &Value, expected: &Value) -> bool {
    expected
        .as_object()
        .is_some_and(|o| o.iter().all(|(k, v)| value.get(k) == Some(v)))
}
fn lookup<'a>(value: &'a Value, path: &Value) -> Result<&'a Value> {
    let mut value = value;
    for p in path
        .as_array()
        .ok_or_else(|| refuse("declaration-invalid"))?
    {
        value = if let Some(i) = p.as_u64() {
            value.get(i as usize)
        } else {
            value.get(string(p)?)
        }
        .ok_or_else(|| refuse("precondition-result-missing"))?;
    }
    Ok(value)
}

// Refuse unknown validating keywords rather than silently weakening a declaration.
fn check_schema(s: &Value, depth: usize) -> Result<()> {
    if depth > 64 {
        return Err(refuse("schema-depth-over-bound"));
    }
    let object = s.as_object().ok_or_else(|| refuse("schema-invalid"))?;
    for (k, v) in object {
        match k.as_str() {
            "type" | "$ref" | "enum" | "const" | "required" | "minimum" | "maximum"
            | "exclusiveMinimum" | "exclusiveMaximum" | "maxProperties" | "minProperties"
            | "minLength" | "maxLength" | "minItems" | "maxItems" | "title" | "description"
            | "default" | "examples" | "contentMediaType" => {}
            "format" => {
                if v != "relative-path" {
                    return Err(refuse("schema-format-unsupported"));
                }
            }
            "contentEncoding" => {
                if v != "base64" {
                    return Err(refuse("schema-encoding-unsupported"));
                }
            }
            "uniqueBy" => {
                if !v.as_str().is_some_and(|s| !s.is_empty()) {
                    return Err(refuse("schema-invalid"));
                }
            }
            "pattern" => {
                regex_lite::Regex::new(string(v)?)
                    .map_err(|_| refuse("schema-pattern-unsupported"))?;
            }
            "additionalProperties" => {
                if v.is_object() {
                    check_schema(v, depth + 1)?;
                } else if !v.is_boolean() {
                    return Err(refuse("schema-invalid"));
                }
            }
            "items" => check_schema(v, depth + 1)?,
            "oneOf" | "anyOf" | "allOf" => {
                for sub in v.as_array().ok_or_else(|| refuse("schema-invalid"))? {
                    check_schema(sub, depth + 1)?;
                }
            }
            "properties" | "$defs" => {
                for sub in v
                    .as_object()
                    .ok_or_else(|| refuse("schema-invalid"))?
                    .values()
                {
                    check_schema(sub, depth + 1)?;
                }
            }
            _ => return Err(refuse("schema-keyword-unsupported")),
        }
    }
    Ok(())
}

#[path = "app_interface_transport.rs"]
mod transport;

fn project(
    op: &Value,
    value: Value,
    args: &Value,
    context: &Value,
    results: &Value,
) -> Result<Value> {
    let Some(p) = op.get("projection") else {
        return Ok(value);
    };
    let expected = resolve(&p["where"], args, context, results)?;
    let collection = value
        .get(string(&p["collection"])?)
        .ok_or_else(|| refuse("projection-shape-invalid"))?;
    let rows: Vec<&Value> = if p["values"] == true {
        collection
            .as_object()
            .ok_or_else(|| refuse("projection-shape-invalid"))?
            .values()
            .collect()
    } else {
        collection
            .as_array()
            .ok_or_else(|| refuse("projection-shape-invalid"))?
            .iter()
            .collect()
    };
    if rows.iter().any(|v| !v.is_object()) {
        return Err(refuse("projection-shape-invalid"));
    }
    Ok(Value::Array(
        rows.into_iter()
            .filter(|v| matches_fields(v, &expected))
            .cloned()
            .collect(),
    ))
}

fn await_bounds(wait: &Value) -> Result<(usize, f64, Vec<u16>)> {
    let bad = || refuse("declaration-await-invalid");
    let o = wait.as_object().ok_or_else(bad)?;
    if o.len() != 3 {
        return Err(bad());
    }
    let attempts = wait["attempts"]
        .as_u64()
        .filter(|n| (1..=20).contains(n))
        .ok_or_else(bad)?;
    let interval = wait["intervalSeconds"]
        .as_f64()
        .filter(|n| (0.0..=3.0).contains(n))
        .ok_or_else(bad)?;
    let statuses = wait["retryStatuses"].as_array().ok_or_else(bad)?;
    if statuses.len() > 3 {
        return Err(bad());
    }
    let mut retry = vec![];
    for s in statuses {
        let s = s
            .as_u64()
            .filter(|s| (502..=504).contains(s))
            .ok_or_else(bad)? as u16;
        if retry.contains(&s) {
            return Err(bad());
        }
        retry.push(s)
    }
    Ok((attempts as usize, interval, retry))
}
fn scenario_assertions(
    value: &Value,
    checks: Option<&Value>,
    context: &Value,
    results: &Value,
) -> Result<()> {
    if let Some(checks) = checks {
        for check in checks
            .as_array()
            .ok_or_else(|| refuse("declaration-invalid"))?
        {
            let ok = if let Some(expected) = check.get("containsText") {
                let expected = scalar(&resolve(expected, &json!({}), context, results)?)?;
                let got = if let Some(path) = check.get("path") {
                    lookup(value, path).ok()
                } else {
                    Some(value)
                };
                got.and_then(Value::as_str)
                    .is_some_and(|s| s.contains(&expected))
            } else if let Some(expected) = check.get("contains") {
                let expected = resolve(expected, &json!({}), context, results)?;
                value.as_array().is_some_and(|a| {
                    a.iter().any(|v| {
                        if expected.is_object() {
                            matches_fields(v, &expected)
                        } else {
                            *v == expected
                        }
                    })
                })
            } else {
                lookup(value, &check["path"]).is_ok_and(|got| {
                    resolve(&check["equals"], &json!({}), context, results)
                        .is_ok_and(|expected| *got == expected)
                })
            };
            if !ok {
                return Err(refuse("readback-mismatch"));
            }
        }
    }
    Ok(())
}

fn rss(body: &[u8], limit: usize) -> Result<Value> {
    let text = std::str::from_utf8(body).map_err(|_| refuse("rss-response-invalid"))?;
    let upper = text.to_ascii_uppercase();
    if text.contains('\0') || upper.contains("<!DOCTYPE") || upper.contains("<!ENTITY") {
        return Err(refuse("rss-xml-unsafe"));
    }
    let doc = roxmltree::Document::parse(text).map_err(|_| refuse("rss-response-invalid"))?;
    let root = doc.root_element();
    if !root.has_tag_name("rss")
        || root.tag_name().namespace().is_some()
        || root.attribute("version") != Some("2.0")
    {
        return Err(refuse("rss-response-invalid"));
    }
    let channels: Vec<_> = root
        .children()
        .filter(|n| n.has_tag_name("channel") && n.tag_name().namespace().is_none())
        .collect();
    if channels.len() != 1 {
        return Err(refuse("rss-response-invalid"));
    }
    let mut out = vec![];
    let mut ids = std::collections::BTreeSet::new();
    for item in channels[0]
        .children()
        .filter(|n| n.has_tag_name("item") && n.tag_name().namespace().is_none())
    {
        if out.len() >= limit {
            return Err(refuse("rss-items-over-bound"));
        }
        let mut fields = std::collections::BTreeMap::new();
        let mut enclosure = Value::Null;
        for child in item.children().filter(|n| n.is_element()) {
            if child.tag_name().namespace().is_some() {
                continue;
            }
            let name = child.tag_name().name();
            if matches!(name, "guid" | "title" | "link" | "description" | "pubDate") {
                if fields
                    .insert(name, child.text().map(str::to_owned))
                    .is_some()
                {
                    return Err(refuse("rss-response-invalid"));
                }
            } else if name == "enclosure" {
                if !enclosure.is_null() {
                    return Err(refuse("rss-response-invalid"));
                }
                let url = child
                    .attribute("url")
                    .filter(|s| !s.is_empty())
                    .ok_or_else(|| refuse("rss-response-invalid"))?;
                let kind = child
                    .attribute("type")
                    .filter(|s| !s.is_empty())
                    .ok_or_else(|| refuse("rss-response-invalid"))?;
                let len = child
                    .attribute("length")
                    .filter(|s| !s.is_empty() && s.bytes().all(|b| b.is_ascii_digit()))
                    .and_then(|s| s.parse::<u64>().ok())
                    .ok_or_else(|| refuse("rss-response-invalid"))?;
                enclosure = json!({"url":url,"bytes":len,"type":kind});
            }
        }
        let id = fields
            .get("guid")
            .and_then(Option::as_ref)
            .or_else(|| fields.get("link").and_then(Option::as_ref))
            .filter(|s| !s.is_empty())
            .ok_or_else(|| refuse("rss-item-identity-missing"))?;
        if !ids.insert(id.clone()) {
            return Err(refuse("rss-item-duplicate"));
        }
        out.push(json!({"id":id,"title":fields.get("title").and_then(Option::as_ref),"link":fields.get("link").and_then(Option::as_ref),"description":fields.get("description").and_then(Option::as_ref),"published":fields.get("pubDate").and_then(Option::as_ref),"enclosure":enclosure}));
    }
    Ok(json!(out))
}

fn compound_readback(op: &Value) -> bool {
    let b = &op["binding"];
    if b["protocol"] != "conversation" {
        return false;
    }
    let Some(steps) = b["steps"].as_array() else {
        return false;
    };
    let Some(last) = steps
        .iter()
        .rposition(|s| ["send", "emit", "http"].iter().any(|k| s.get(k).is_some()))
    else {
        return false;
    };
    let mut captures = std::collections::BTreeSet::new();
    for step in &steps[last + 1..] {
        if step["receive"]["where"]
            .as_array()
            .is_some_and(|a| !a.is_empty())
        {
            if let Some(id) = step["id"].as_str() {
                captures.insert(id.to_owned());
            }
        }
        if let Some(terminals) = step["receiveAll"].as_array() {
            for t in terminals {
                if t["where"].as_array().is_some_and(|a| !a.is_empty()) {
                    if let Some(id) = t["id"].as_str() {
                        captures.insert(id.to_owned());
                    }
                }
            }
        }
    }
    fn uses(v: &Value, ids: &std::collections::BTreeSet<String>) -> bool {
        if let Some(o) = v.as_object() {
            if o.len() == 1 && o.contains_key("result") {
                return v["result"][0].as_str().is_some_and(|s| ids.contains(s));
            }
            o.values().any(|v| uses(v, ids))
        } else {
            v.as_array().is_some_and(|a| a.iter().any(|v| uses(v, ids)))
        }
    }
    uses(&b["result"], &captures)
}

fn utc_iso(ms: u64) -> Result<String> {
    let days = (ms / 86400000) as i64;
    let z = days + 719468;
    let era = if z >= 0 { z } else { z - 146096 } / 146097;
    let doe = z - era * 146097;
    let yoe = (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365;
    let mut y = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = doy - (153 * mp + 2) / 5 + 1;
    let m = mp + if mp < 10 { 3 } else { -9 };
    y += if m <= 2 { 1 } else { 0 };
    if y > 9999 {
        return Err(refuse("controller-time-invalid"));
    }
    let seconds = ms / 1000;
    Ok(format!(
        "{y:04}-{m:02}-{d:02}T{:02}:{:02}:{:02}.{:03}Z",
        seconds / 3600 % 24,
        seconds / 60 % 60,
        seconds % 60,
        ms % 1000
    ))
}
