#!/usr/bin/env python3
"""Check allocated request bytes against the concrete Host/transport dispatchers.
This deliberately parses a small known grammar, not arbitrary Lean/Rust. Unknown
shapes fail closed. Responses, nested codec tags and arbitrary literals are not
request allocations. No Lean compiler or service is needed.
"""
import argparse
import json
import os
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parent.parent
REGISTRY = Path("protocol/host-operations.json")
GENERATED = Path("native/host-operations.rs")
GENERATED_LEAN = Path("Host/HostOperations.lean")

class Invalid(ValueError):
    pass

def require(condition, reason):
    if not condition:
        raise Invalid(reason)

def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, f"duplicate JSON object key: {key}")
        result[key] = value
    return result

def load(root):
    data = json.loads((root / REGISTRY).read_text(), object_pairs_hook=unique_object)
    require(data.get("format") == "mini-host-request-operations-v1", "unknown operation registry format")
    require(set(data) == {"format", "operations", "response_markers", "consent_plans", "consent_exempt", "client_constants", "consent_frames", "ordinary_headers", "dav_methods", "dav_headers", "dav_header_rules"}, "unknown registry fields")
    ids, symbols = {}, set()
    for entry in data["operations"]:
        require(set(entry) == {"code", "symbol", "status", "routes", "owner", "purpose", "receiver", "effect"}, f"invalid operation fields: {entry}")
        code, symbol = entry["code"], entry["symbol"]
        require(type(code) is int and 0 <= code <= 255, f"invalid request byte: {code}")
        require(code not in ids, f"duplicate request allocation: {code}")
        require(isinstance(symbol, str) and re.fullmatch(r"[A-Z][A-Z0-9_]*", symbol), f"invalid operation symbol: {symbol}")
        require(symbol not in symbols, f"duplicate operation symbol: {symbol}")
        require(entry["status"] in {"active", "reserved"}, f"invalid allocation status: {symbol}")
        require(entry["routes"] in [[], ["operator"], ["public", "operator"]], f"invalid routes: {symbol}")
        require(all(isinstance(entry[k], str) and entry[k].strip() for k in ["owner", "purpose"]), f"missing owner/purpose: {symbol}")
        require(entry["receiver"] in {"dispatchSession", "fnDispatch", "serveFrame", None}, f"unknown receiver: {symbol}")
        require((entry["status"] == "reserved") == (entry["receiver"] is None), f"receiver/status mismatch: {symbol}")
        # effect: whether the receiver can append to the durable log. A thrown handler on an `append`
        # operation is answered undecided (255), never NO_RECORD (Host/RequestRefusal.lean exceptionAnswer).
        require(entry["effect"] in {"none", "append"}, f"invalid effect: {symbol}")
        require(entry["status"] == "active" or entry["effect"] == "none", f"reserved operation with an effect: {symbol}")
        require(not (entry["status"] == "active" and symbol.endswith("_SUBMIT")) or entry["effect"] == "append",
                f"active submit operation without effect append: {symbol}")
        ids[code] = entry
        symbols.add(symbol)
    responses, markers = set(), set()
    for entry in data["response_markers"]:
        require(set(entry) == {"code", "symbol", "purpose", "request_reserved"} and type(entry["code"]) is int and type(entry["request_reserved"]) is bool, "invalid response marker")
        require(0 <= entry["code"] <= 255 and entry["code"] not in responses, "duplicate/invalid response marker")
        require(isinstance(entry["symbol"], str) and re.fullmatch(r"[A-Z][A-Z0-9_]*", entry["symbol"]), f"invalid response marker symbol: {entry['symbol']}")
        require(entry["symbol"] not in markers, f"duplicate response marker symbol: {entry['symbol']}")
        markers.add(entry["symbol"])
        require(not entry["request_reserved"] or entry["code"] not in ids, f"request collides with reserved response marker: {entry['code']}")
        responses.add(entry["code"])
    # The operator plans a client checks against its local consent provider (frame 224) before any
    # signing consumer sees the operator's reply. Each must be an active allocation, listed once.
    plans = data["consent_plans"]
    require(isinstance(plans, list) and all(isinstance(p, str) for p in plans), "consent_plans must be a list of operation symbols")
    require(len(set(plans)) == len(plans), "duplicate consent plan")
    by_symbol = {e["symbol"]: e for e in ids.values()}
    for plan in plans:
        require(plan in by_symbol and by_symbol[plan]["status"] == "active", f"consent plan is not an active operation: {plan}")
    # Every active signing-plan operation (symbol *_PLAN, *_READY, *_PREPARE) is either consent-checked
    # (consent_plans) or recorded as exempt WITH its reason (consent_exempt); an unlisted one refuses by name.
    exempt = data["consent_exempt"]
    require(isinstance(exempt, dict) and all(isinstance(k, str) and isinstance(v, str) and v.strip() for k, v in exempt.items()), "consent_exempt must map operation symbols to a non-empty reason")
    for symbol in exempt:
        require(symbol in by_symbol and by_symbol[symbol]["status"] == "active", f"consent_exempt names no active operation: {symbol}")
        require(symbol not in plans, f"consent_exempt and consent_plans both list: {symbol}")
    for symbol, entry in by_symbol.items():
        if entry["status"] == "active" and re.search(r"_(PLAN|READY|PREPARE)$", symbol):
            require(symbol in plans or symbol in exempt, f"signing-plan operation neither consent-checked nor recorded exempt: {symbol}")
    # The local consent provider's frames (Host/ClientConsentCore.lean): a namespace of their own,
    # 220..239, never a request allocation.
    frames = set()
    for entry in data["consent_frames"]:
        require(set(entry) == {"code", "symbol", "purpose"} and type(entry["code"]) is int, f"invalid consent frame: {entry}")
        require(220 <= entry["code"] <= 239 and entry["code"] not in frames, f"duplicate/out-of-namespace consent frame: {entry['code']}")
        require(entry["code"] not in ids, f"consent frame collides with a request allocation: {entry['code']}")
        require(re.fullmatch(r"CONSENT_[A-Z0-9_]+", entry["symbol"]) and entry["symbol"] not in symbols, f"invalid consent frame symbol: {entry['symbol']}")
        require(isinstance(entry["purpose"], str) and entry["purpose"].strip(), f"consent frame without purpose: {entry['symbol']}")
        frames.add(entry["code"])
    for code in ids:
        require(not 220 <= code <= 239, f"request allocation inside the consent frame namespace: {code}")
    # Lean's ordinaryHeaderName (Kernel/ApplicationDispatchAdmission.lean), emitted for every Rust reader.
    headers = data["ordinary_headers"]
    require(isinstance(headers, list) and headers and all(isinstance(h, str) and re.fullmatch(r"[a-z0-9-]+", h) for h in headers) and len(set(headers)) == len(headers), "ordinary_headers must be distinct lowercase header names")
    # Lean's davMethod and davHeaderName: the WebDAV/CalDAV calls and their parameter headers.
    for field, pattern in (("dav_methods", r"[A-Z]+"), ("dav_headers", r"[a-z0-9-]+")):
        names = data[field]
        require(isinstance(names, list) and names and all(isinstance(n, str) and re.fullmatch(pattern, n) for n in names) and len(set(names)) == len(names), f"{field} must be distinct names")
    require(not set(data["dav_headers"]) & set(headers), "dav_headers must not be ordinary headers")
    for rule in data["dav_header_rules"]:
        require(set(rule) == {"name", "methods", "values"}, "invalid DAV header rule")
        require(rule["name"] in data["dav_headers"] and rule["methods"] and set(rule["methods"]) <= set(data["dav_methods"]), "invalid DAV method/header rule")
        require(all(isinstance(v, str) and v for v in rule["values"]), "invalid DAV values")
    require([r["name"] for r in data["dav_header_rules"]] == data["dav_headers"], "DAV rules must cover each header exactly once")
    bindings = set()
    for binding in data["client_constants"]:
        require(set(binding) == {"path", "constant", "operation"}, "invalid client constant binding")
        path = Path(binding["path"])
        require(not path.is_absolute() and ".." not in path.parts and path.suffix == ".rs", "invalid client constant path")
        require(re.fullmatch(r"[A-Z][A-Z0-9_]*", binding["constant"]), "invalid client constant name")
        require(binding["operation"] in symbols, "client constant names unknown operation")
        key = (binding["path"], binding["constant"])
        require(key not in bindings, f"duplicate client constant binding: {key}")
        bindings.add(key)
    return data, ids

RUST_RAW = re.compile(r'(?:br|r)(#*)"')
RUST_CHAR = re.compile(r"'(?:[^'\\\n]|\\(?:x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]+\}|.))'")

def masked(source, language):
    """Preserve offsets/newlines while masking comments and literal contents.

    Handles nested Lean/Rust block comments, line comments, escaped strings,
    Rust raw strings and character literals. Unclosed constructs refuse.
    """
    result = list(source)
    block_open, block_close = ("/-", "-/") if language == "lean" else ("/*", "*/")
    line = "--" if language == "lean" else "//"
    def blank(start, end):
        for j in range(start, end):
            if result[j] != "\n": result[j] = " "
    i = 0
    while i < len(source):
        if source.startswith(line, i):
            end = source.find("\n", i)
            end = len(source) if end < 0 else end
            blank(i, end); i = end; continue
        if source.startswith(block_open, i):
            start, depth = i, 1
            i += 2
            while i < len(source) and depth:
                if source.startswith(block_open, i): depth += 1; i += 2
                elif source.startswith(block_close, i): depth -= 1; i += 2
                else: i += 1
            require(depth == 0, "unclosed source block comment")
            blank(start, i); continue
        # Positional matches (pattern.match(source, i)), never source[i:]: a slice per character is
        # quadratic, and the literal scan masks every file of five crates.
        if language == "rust" and source[i] in "rb'":
            raw = RUST_RAW.match(source, i)
            if raw:
                end_marker = '"' + raw[1]
                end = source.find(end_marker, raw.end())
                require(end >= 0, "unclosed Rust raw string")
                end += len(end_marker); blank(i, end); i = end; continue
            character = RUST_CHAR.match(source, i)
            if character:
                end = character.end(); blank(i, end); i = end; continue
        if source[i] == '"':
            start = i; i += 1
            while i < len(source) and source[i] != '"':
                i += 2 if source[i] == "\\" else 1
            require(i < len(source), "unclosed source string")
            i += 1; blank(start, i); continue
        i += 1
    return "".join(result)

def balanced_end(source, start):
    pairs = {"(": ")", "[": "]", "{": "}"}
    require(start < len(source) and source[start] in pairs, "expected balanced delimiter")
    stack = [pairs[source[start]]]
    for i in range(start + 1, len(source)):
        if source[i] in pairs: stack.append(pairs[source[i]])
        elif source[i] in pairs.values():
            require(stack and source[i] == stack.pop(), "mismatched source delimiter")
            if not stack: return i + 1
    raise Invalid("unclosed source delimiter")

def lean_function(source, name):
    starts = list(re.finditer(rf"^(?:private |partial )?def {re.escape(name)}\b", source, re.M))
    require(len(starts) == 1, f"expected exactly one Lean def {name}")
    start = starts[0].start()
    end = re.search(r"^(?:private |partial )?(?:def|theorem|structure|inductive|abbrev)\b", source[starts[0].end():], re.M)
    return source[start:starts[0].end() + end.start() if end else len(source)]

def numeric_lean_arms(block, label):
    matches = list(re.finditer(r"^( *)match operation with\s*$", block, re.M))
    require(len(matches) == 1, f"{label}: expected one direct match operation with")
    match = matches[0]
    indent = len(match[1])
    remainder = block[match.end():]
    arms = list(re.finditer(rf"^ {{{indent}}}\| (.+?) =>", remainder, re.M))
    markers = list(re.finditer(rf"^ {{{indent}}}\|", remainder, re.M))
    require(len(markers) == len(arms), f"{label}: unsupported multiline/unknown arm header")
    require(arms and arms[-1][1] == "_", f"{label}: missing final fallback arm")
    codes = []
    for arm in arms[:-1]:
        require(re.fullmatch(r"\d+(?:\s*\|\s*\d+)*", arm[1]), f"{label}: unknown request pattern {arm[1]}")
        codes.extend(int(n) for n in re.findall(r"\d+", arm[1]))
    require(len(codes) == len(set(codes)), f"{label}: duplicate request arm")
    require(all(0 <= code <= 255 for code in codes), f"{label}: request outside byte namespace")
    return codes

def host_receivers(source):
    source = masked(source, "lean")
    direct = lean_function(source, "dispatchSession")
    direct_match = re.search(r"^ *match operation with", direct, re.M)
    require(direct_match is not None, "dispatchSession: missing direct match")
    header_end = direct.find(":= do")
    require(header_end >= 0 and not direct[header_end + len(":= do"):direct_match.start()].strip(), "dispatchSession: unsupported logic before operation match")
    groups = {"dispatchSession": numeric_lean_arms(direct, "dispatchSession")}
    starts = list(re.finditer(r"\blet fnDispatch\s*:", source))
    require(len(starts) == 1, "expected one local fnDispatch dispatcher")
    start = starts[0].start()
    end = source.find("let meteringProfile :=", start)
    require(end > start, "fnDispatch: missing known dispatcher boundary")
    local = source[start:end]
    prefix = local[:local.index("match operation with")]
    require(re.fullmatch(r"let fnDispatch\s*:\s*UInt8\s*→\s*List UInt8\s*→\s*IO \(UInt8 × List UInt8\)\s*:=\s*fun operation payload => do\s*try\s*", prefix), "fnDispatch: unsupported dispatcher wrapper")
    groups["fnDispatch"] = numeric_lean_arms(local, "fnDispatch")
    # An exact delegation is a routing edge, not a second implementation.
    # Any extra logic or changed arguments keeps the arm a concrete receiver.
    direct_arms = list(re.finditer(r"^  \| (.+?) =>", direct, re.M))
    forwarded = []
    for index, arm in enumerate(direct_arms[:-1]):
        body = direct[arm.end():direct_arms[index + 1].start()].strip()
        if body == "fnDispatch operation payload":
            forwarded.extend(int(n) for n in re.findall(r"\d+", arm[1]))
    require(set(forwarded) <= set(groups["fnDispatch"]), "dispatchSession: forwarding lacks fnDispatch receiver")
    groups["dispatchSession"] = [code for code in groups["dispatchSession"] if code not in forwarded]
    frame = lean_function(source, "serveFrame")
    require("dispatchSession config state" in frame, "serveFrame: missing ordinary dispatch fallback")
    chain_start = frame.find("\n  try\n")
    chain_end = frame.find("\n    else\n      let started", chain_start)
    require(chain_start >= 0 and chain_end > chain_start, "serveFrame: unsupported dispatch chain boundary")
    chain = frame[chain_start:chain_end]
    interceptions = re.findall(r"^    (?:else )?if (operation == \d+(?: \|\| operation == \d+)*) then\s*$", chain, re.M)
    conditionals = re.findall(r"^ *?(?:else )?if\b", chain, re.M)
    require(interceptions and len(interceptions) == len(conditionals), "serveFrame: unknown interception shape")
    groups["serveFrame"] = [int(n) for condition in interceptions for n in re.findall(r"operation == (\d+)", condition)]
    require(all(0 <= code <= 255 for code in groups["serveFrame"]), "serveFrame: request outside byte namespace")
    result = {}
    for receiver, codes in groups.items():
        for code in codes:
            require(code not in result, f"Host: duplicate/shadowed request {code}: {result.get(code)} and {receiver}")
            result[code] = receiver
    return result

def rust_function(source, name):
    hits = list(re.finditer(rf"\bfn {re.escape(name)}\s*\(", source))
    require(len(hits) == 1, f"expected one Rust function {name}")
    brace = source.find("{", hits[0].end())
    require(brace >= 0, f"{name}: missing function body")
    return source[brace + 1:balanced_end(source, brace) - 1]

def selector_codes(selector, symbols):
    codes = []
    for part in selector.split("|"):
        part = part.strip()
        if re.fullmatch(r"\d+", part): codes.append(int(part)); continue
        interval = re.fullmatch(r"(\d+)\s*\.\.=\s*(\d+)", part)
        if interval:
            first, last = map(int, interval.groups())
            require(0 <= first <= last <= 255, "invalid opcode selector range")
            codes.extend(range(first, last + 1)); continue
        symbol = re.fullmatch(r"(?:crate::|mini_sdk::)?host_operations::([A-Z][A-Z0-9_]*)", part)
        require(symbol and symbol[1] in symbols, f"unknown Rust opcode selector: {part}")
        codes.append(symbols[symbol[1]])
    require(codes and all(0 <= n <= 255 for n in codes), "invalid Rust operation selector")
    return codes

def rust_routes(source, name, symbols):
    source = masked(source, "rust")
    body = rust_function(source, name)
    match = re.search(r"\bmatch request\s*\{", body)
    require(match is not None, f"{name}: expected match request")
    require(not body[:match.start()].strip(), f"{name}: unknown pre-match logic")
    brace = body.index("{", match.start())
    end = balanced_end(body, brace)
    require(not body[end:].strip(), f"{name}: unknown post-match logic")
    arms = body[brace + 1:end - 1]
    i, codes = 0, []
    while i < len(arms):
        while i < len(arms) and arms[i].isspace(): i += 1
        if i == len(arms): break
        if arms[i] == "_":
            require(re.fullmatch(r"_\s*=>\s*false\s*,?\s*", arms[i:]), f"{name}: unknown fallback")
            return set(codes)
        require(arms[i] == "[", f"{name}: expected byte-slice match arm")
        pattern_end = balanced_end(arms, i)
        selector = arms[i + 1:pattern_end - 1].split(",", 1)[0]
        added = selector_codes(selector, symbols)
        require(not set(added).intersection(codes) and len(added) == len(set(added)), f"{name}: duplicate/shadowed selector {selector}")
        codes.extend(added)
        i = pattern_end
        # Optional Rust guard, with balanced subexpressions. Do not parse its
        # semantic conditions: runtime receiving tests still own those bounds.
        while i < len(arms) and not arms.startswith("=>", i):
            if arms[i] in "([{": i = balanced_end(arms, i)
            else: i += 1
        require(i < len(arms), f"{name}: missing match arrow")
        i += 2
        while i < len(arms) and arms[i].isspace(): i += 1
        if i < len(arms) and arms[i] == "{":
            i = balanced_end(arms, i)
            while i < len(arms) and arms[i].isspace(): i += 1
            if i < len(arms) and arms[i] == ",": i += 1
        else:
            while i < len(arms) and arms[i] != ",":
                if arms[i] in "([{": i = balanced_end(arms, i)
                else: i += 1
            require(i < len(arms), f"{name}: expression arm missing comma")
            i += 1
    raise Invalid(f"{name}: missing false fallback")

def no_append(data):
    """Active operations whose receiver never appends to the durable log (effect: none)."""
    return sorted(e["code"] for e in data["operations"] if e["status"] == "active" and e["effect"] == "none")

def by_symbol_codes(data):
    return {e["symbol"]: e["code"] for e in data["operations"]}

def plan_codes(data):
    by_symbol = {e["symbol"]: e["code"] for e in data["operations"]}
    return [by_symbol[p] for p in data["consent_plans"]]

def lean_name(symbol):
    parts = symbol.lower().split("_")
    return parts[0] + "".join(part.capitalize() for part in parts[1:])

def generated_lean(data):
    lines = ["module", "", "@[expose] public section", "",
             "/-! Generated by `scripts/host-operations.py generate`; edit `protocol/host-operations.json`.",
             "The Host's copy of the request registry's derived tables: the response markers, the",
             "append-free operation set the answer discipline reads (`Host.RequestRefusal`) and the",
             "consent plan list. No payload codec or admission rule lives here. -/", "",
             "namespace Minidregg.Host.HostOperations", ""]
    for entry in sorted(data["response_markers"], key=lambda e: e["code"]):
        lines += [f"/-- {entry['purpose']} -/", f"def {lean_name(entry['symbol'])}Marker : UInt8 := {entry['code']}", ""]
    lines += ["/-- Active request operations whose receiver never appends to the durable log",
              "(registry `effect: none`). A handler of one of these that throws is answered a",
              "proven no-append refusal; on every other operation it is answered undecided. -/",
              f"def noAppendOperations : List UInt8 := [{', '.join(map(str, no_append(data)))}]", "",
              "/-- The operator plans a client checks against its local consent provider (frame 224)",
              "before any signing consumer sees the reply (registry `consent_plans`). -/",
              f"def consentPlans : List UInt8 := [{', '.join(map(str, plan_codes(data)))}]", "",
              "/-- Signing-plan operations recorded as NOT consent-checked, each with its reason in the",
              "registry (`consent_exempt`). -/",
              f"def consentExemptPlans : List UInt8 := [{', '.join(map(str, sorted(by_symbol_codes(data)[s] for s in data['consent_exempt'])))}]", ""]
    lines += ["/-- The local consent provider's frames (`Host.ClientConsentCore`), a namespace apart from",
              "requests (registry `consent_frames`). -/"]
    for entry in data["consent_frames"]:
        lines += [f"def {lean_name(entry['symbol'])}Frame : UInt8 := {entry['code']}"]
    lines += [f"def consentFrames : List UInt8 := [{', '.join(str(e['code']) for e in data['consent_frames'])}]", "",
              "/-- `Kernel.ApplicationDispatchAdmission.ordinaryHeaderName`'s names (registry `ordinary_headers`). -/",
              "def ordinaryHeaderNames : List String := [" + ", ".join(json.dumps(h) for h in data["ordinary_headers"]) + "]", "",
              "/-- `Kernel.ApplicationDispatchAdmission.davMethod`'s and `davHeaderName`'s names. -/",
              "def davMethodNames : List String := [" + ", ".join(json.dumps(h) for h in data["dav_methods"]) + "]",
              "def davHeaderNames : List String := [" + ", ".join(json.dumps(h) for h in data["dav_headers"]) + "]", "",
              "end Minidregg.Host.HostOperations"]
    return "\n".join(lines) + "\n"

def generated_hosted_dav(data):
    q = lambda xs: "[" + ", ".join(json.dumps(x) for x in xs) + "]"
    rows = ["  (" + json.dumps(r["name"]) + ", " + q(r["methods"]) + ", " + q(r["values"]) + ")" for r in data["dav_header_rules"]]
    return """/- Generated by scripts/host-operations.py; edit protocol/host-operations.json. -/
module
@[expose] public section
namespace Minidregg.Effects.Revival.HostedDav
/-- Physical parameter vocabulary; empty values means nonempty transport text.
Destination origin/prefix resolution is the receiving adapter's custody obligation. -/
def rules : List (String × List String × List String) := [
""" + ",\n".join(rows) + " ]\n" + "def contract : List UInt8 := " + json.dumps("DREGG/HOSTED-DAV/v1:" + json.dumps(data["dav_header_rules"], sort_keys=True, separators=(",", ":"))) + ".toUTF8.toList\n" + """
def headerAllowed (method name value : List UInt8) : Bool :=
  rules.any fun (n, methods, values) =>
    name == n.toUTF8.toList &&
    methods.any (fun m => method == m.toUTF8.toList) &&
    (if values.isEmpty then !value.isEmpty else
      values.any (fun v => value == v.toUTF8.toList))
end Minidregg.Effects.Revival.HostedDav
"""

def generated(data):
    lines = ["// Generated by scripts/host-operations.py generate; edit protocol/host-operations.json.",
             "// Request byte allocations, response markers and the derived operation sets.",
             "// No payload codecs or admission rules live here.",
             "#![allow(dead_code)]", ""]
    for entry in sorted(data["operations"], key=lambda e: e["code"]):
        lines += [f"// {entry['status']}; {','.join(entry['routes']) or 'Host stdio only'}; owner: {entry['owner']}; effect: {entry['effect']}",
                  f"pub const {entry['symbol']}: u8 = {entry['code']};"]
    lines += ["", "// Response markers: the first byte of a reply frame, a namespace apart from requests."]
    for entry in data["response_markers"]:
        lines += [f"// {entry['purpose']}", f"pub const RESPONSE_{entry['symbol']}: u8 = {entry['code']};"]
    lines += ["", "// Operator plans checked against the local consent provider (frame 224) before signing."]
    lines += ["pub const CONSENT_PLANS: &[u8] = &[" + ", ".join(p for p in data["consent_plans"]) + "];"]
    lines += ["", "// Signing-plan operations recorded as NOT consent-checked, each with its reason in the registry (consent_exempt)."]
    lines += ["pub const CONSENT_EXEMPT_PLANS: &[u8] = &[" + ", ".join(sorted(data["consent_exempt"])) + "];"]
    lines += ["", "// Active operations whose receiver never appends to the durable log (effect: none).",
              "// A reply under RESPONSE_HOST_OUTCOME to any operation is undecided; to one of these it still only ever means undecided.",
              f"pub const NO_APPEND_OPERATIONS: &[u8] = &[{', '.join(map(str, no_append(data)))}];"]
    lines += ["", "// The local consent provider's frames (Host/ClientConsentCore.lean), a namespace apart from requests."]
    for entry in data["consent_frames"]:
        lines += [f"// {entry['purpose']}", f"pub const {entry['symbol']}: u8 = {entry['code']};"]
    lines += ["pub const CONSENT_FRAMES: &[u8] = &[" + ", ".join(e["symbol"] for e in data["consent_frames"]) + "];"]
    lines += ["", "// Kernel/ApplicationDispatchAdmission.lean ordinaryHeaderName: the signed ordinary request headers.",
              "pub const ORDINARY_HEADER_NAMES: &[&str] = &[" + ", ".join(json.dumps(h) for h in data["ordinary_headers"]) + "];",
              "pub fn ordinary_header_name(name: &str) -> bool {", "    ORDINARY_HEADER_NAMES.contains(&name)", "}",
              "// Kernel/ApplicationDispatchAdmission.lean refererValueOk: a signed referer is a path of the grain's own origin.",
              "pub fn referer_value_ok(value: &str) -> bool {",
              "    let bytes = value.as_bytes();",
              "    bytes.first() == Some(&b'/') && bytes.get(1) != Some(&b'/') && !bytes.contains(&b'\\\\')",
              "}",
              "// Kernel/ApplicationDispatchAdmission.lean ordinaryHeaderOk: by name, and a referer also by value.",
              "pub fn ordinary_header_ok(name: &str, value: &str) -> bool {",
              "    ordinary_header_name(name) && (name != \"referer\" || referer_value_ok(value))",
              "}",
              "/// The sender's reduction of a referer before signing: a path passes; an absolute http(s) URL whose",
              "/// authority is `authority` (the grain's own origin) becomes its path and query; anything else is",
              "/// dropped (None), never refused. Every Some satisfies referer_value_ok.",
              "pub fn same_origin_referer(value: &str, authority: Option<&str>) -> Option<String> {",
              "    let value = value.split('#').next().unwrap_or_default();",
              "    if referer_value_ok(value) {",
              "        return Some(value.to_owned());",
              "    }",
              "    let rest = [\"https://\", \"http://\"].iter().find_map(|scheme| {",
              "        value.get(..scheme.len()).filter(|p| p.eq_ignore_ascii_case(scheme)).map(|_| &value[scheme.len()..])",
              "    })?;",
              "    let end = rest.find(['/', '?']).unwrap_or(rest.len());",
              "    if !authority.is_some_and(|a| !a.is_empty() && rest[..end].eq_ignore_ascii_case(a)) {",
              "        return None;",
              "    }",
              "    let path = match &rest[end..] {",
              "        \"\" => \"/\".to_owned(),",
              "        tail if tail.starts_with('?') => format!(\"/{tail}\"),",
              "        tail => tail.to_owned(),",
              "    };",
              "    referer_value_ok(&path).then_some(path)",
              "}",
              "", "// Kernel/ApplicationDispatchAdmission.lean davMethod: the WebSession DAV calls, each an exchange.",
              "pub const DAV_METHODS: &[&str] = &[" + ", ".join(json.dumps(h) for h in data["dav_methods"]) + "];",
              "pub fn dav_method(name: &str) -> bool {", "    DAV_METHODS.contains(&name)", "}",
              "// Kernel/ApplicationDispatchAdmission.lean davHeaderName: signed, admitted on a DAV method only.",
              "pub const DAV_HEADER_NAMES: &[&str] = &[" + ", ".join(json.dumps(h) for h in data["dav_headers"]) + "];",
              "pub fn dav_header_name(name: &str) -> bool {", "    DAV_HEADER_NAMES.contains(&name)", "}"]
    lines += ["", "pub fn dav_header_allowed(method: &str, name: &str, value: &str) -> bool {", "    DAV_HEADER_RULES.iter().any(|(n, methods, values)| *n == name && methods.contains(&method) && if values.is_empty() { !value.is_empty() } else { values.contains(&value) })", "}", "pub const DAV_HEADER_RULES: &[(&str, &[&str], &[&str])] = &["]
    for r in data["dav_header_rules"]:
        lines.append("    (" + json.dumps(r["name"]) + ", &[" + ", ".join(json.dumps(m) for m in r["methods"]) + "], &[" + ", ".join(json.dumps(v) for v in r["values"]) + "]),")
    lines.append("];")
    return "\n".join(lines) + "\n"

# The Rust crates that speak the Host wire (each can name the generated constants).
WIRE_CRATES = ["mini-sdk", "resource-client", "spk-host", "discord-entrance", "grain-runtime"]
OP_PARAMETERS = {"operation", "op", "opcode", "request_op", "op_code", "operation_byte", "request_operation"}
EXEMPT_MARK = "not-a-host-op"

def _arguments(source, start):
    """Top-level argument spans of the call/signature whose `(` ends just before `start`."""
    depth, spans, current = 0, [], start
    for i in range(start, len(source)):
        ch = source[i]
        if ch in "([{": depth += 1
        elif ch in ")]}":
            if depth == 0:
                spans.append((current, i)); return spans
            depth -= 1
        elif ch == "," and depth == 0:
            spans.append((current, i)); current = i + 1
    return spans

def rust_literals(root, data):
    """Every request byte or consent frame written as a decimal literal in a wire crate where the
    callee's own signature types the argument as an operation (`operation: u8`, `op: u8`, ...), or
    bound to an `*_OP`/`*_OPERATION`/`*_OPCODE` constant. Such a byte names its generated constant
    (native/host-operations.rs); a line marked `not-a-host-op` (same or previous line) is exempt.
    Returns (findings, unregistered): `path:line callee value SYMBOL` rows, and consent-namespace
    literals (220..239) that no registry entry names."""
    named = {e["code"]: e["symbol"] for e in data["operations"]}
    named.update({e["code"]: e["symbol"] for e in data["consent_frames"]})
    markers = {e["code"]: "RESPONSE_" + e["symbol"] for e in data["response_markers"] if e["code"] >= 253}
    named.update(markers)
    files = [f for crate in WIRE_CRATES for f in sorted((root / "native" / crate).rglob("*.rs"))
             if "target" not in f.parts and f.name != GENERATED.name]
    sources = {f: f.read_text() for f in files}
    masks = {f: masked(text, "rust") for f, text in sources.items()}
    callees = {}
    signature = re.compile(r"\bfn\s+(\w+)\s*(?:<[^{(]*?>)?\s*\(", re.S)
    for f, text in masks.items():
        crate = f.relative_to(root).parts[1]
        for m in signature.finditer(text):
            spans = _arguments(text, m.end())
            method = bool(spans) and text[spans[0][0]:spans[0][1]].strip().endswith("self")
            for index, (a, b) in enumerate(spans):
                param = re.fullmatch(r"(?:mut\s+)?(\w+)\s*:\s*u8", text[a:b].strip())
                if param and param[1] in OP_PARAMETERS:
                    callees.setdefault((crate, m[1]), set()).add(index - method)
    findings, unregistered = [], []
    def report(f, offset, callee, value):
        line = masks[f].count("\n", 0, offset) + 1
        lines = sources[f].splitlines()
        if EXEMPT_MARK in lines[line - 1] or (line > 1 and EXEMPT_MARK in lines[line - 2]): return
        row = f"{f.relative_to(root)}:{line} {callee} {value} {named.get(value, '?')}"
        if value in named: findings.append(row)
        elif 220 <= value <= 239: unregistered.append(row)
    call = re.compile(r"(?<![\w])(\w+)\s*(?:::<[^>]*>)?\s*\(")
    for f, text in masks.items():
        crate = f.relative_to(root).parts[1]
        for m in call.finditer(text):
            key = (crate, m[1])
            if key not in callees or text[max(0, m.start() - 3):m.start()].rstrip().endswith("fn"): continue
            spans = _arguments(text, m.end())
            for index in callees[key]:
                if index < len(spans):
                    a, b = spans[index]
                    literal = re.fullmatch(r"\s*(\d+)(?:u8)?\s*", text[a:b])
                    if literal: report(f, a, m[1], int(literal[1]))
        for m in re.finditer(r"\bconst\s+(\w*(?:OP|OPERATION|OPCODE)\w*)\s*:\s*u8\s*=\s*(\d+)(?:u8)?\s*;", text):
            report(f, m.start(), "const " + m[1], int(m[2]))
        # A frame's first byte matched against literals: `matches!(frame.first(), Some(48 | 58))`,
        # `if let Some(220) = request.first()` (an operation, a consent frame or a response marker).
        for m in re.finditer(r"\.first\(\)(?:\.copied\(\))?\s*,\s*Some\(\s*&?\s*(\d+(?:\s*\|\s*&?\s*\d+)*)\s*\)", text):
            for number in re.finditer(r"\d+", m[1]):
                report(f, m.start(1) + number.start(), "first()", int(number[0]))
        for m in re.finditer(r"Some\(\s*&?\s*(\d+(?:\s*\|\s*&?\s*\d+)*)\s*\)\s*=\s*[\w.]+\.first\(\)", text):
            for number in re.finditer(r"\d+", m[1]):
                report(f, m.start(1) + number.start(), "first()", int(number[0]))
        # A `match` on an operation-named variable whose top-level arms are literals (`183 =>`,
        # `185 | 186 =>`, `183 if guard =>`).
        for m in re.finditer(r"\bmatch\s+\*?(?:" + "|".join(sorted(OP_PARAMETERS)) + r")\s*\{", text):
            depth, k, seen = 1, m.end(), set()
            while depth and k < len(text):
                c = text[k]
                depth += c == "{"
                depth -= c == "}"
                if depth == 1 and text[k - 1] in ",{\n":
                    arm = re.match(r"\s*(\d+(?:\s*\|\s*\d+)*)\s*(?:if\b[^=]*)?=>", text[k:])
                    if arm and k + arm.start(1) not in seen:
                        seen.add(k + arm.start(1))
                        for number in re.finditer(r"\d+", arm[1]):
                            report(f, k + arm.start(1) + number.start(), "match arm", int(number[0]))
                k += 1
        # A reply's leading byte compared with a marker: `frame[0] != 255`, `reply.first() != Some(&255)`.
        for m in re.finditer(r"\b\w+\s*\[\s*0\s*\]\s*(?:==|!=)\s*(\d+)\b", text):
            if int(m[1]) in markers: report(f, m.start(1), "[0] ==", int(m[1]))
        for m in re.finditer(r"\.first\(\)(?:\.copied\(\))?\s*(?:==|!=)\s*Some\(\s*&?\s*(\d+)\s*\)", text):
            if int(m[1]) in markers: report(f, m.start(1), "first() ==", int(m[1]))
        # A reply classified by its leading marker in a slice pattern: `[255, ..] =>`.
        for m in re.finditer(r"\[\s*(\d+)\s*,\s*(?:\w+\s*@\s*)?\.\.\s*\]\s*(?:=>|\||if\b)", text):
            if int(m[1]) in markers: report(f, m.start(1), "[marker, ..]", int(m[1]))
    return findings, unregistered

def lean_ordinary_headers(root):
    source = (root / LEAN_HEADERS).read_text()
    m = re.search(r"def ordinaryHeaderName\b.*?:=\s*\(\[(.*?)\]\s*:\s*List String\)", source, re.S)
    require(m, "Kernel/ApplicationDispatchAdmission.lean ordinaryHeaderName: shape not recognised")
    return re.findall(r'"([^"]*)"', m[1])

def lean_string_list(root, definition):
    source = (root / "Kernel/ApplicationDispatchAdmission.lean").read_text()
    m = re.search(r"def " + definition + r"\b.*?:=\s*\(\[(.*?)\]\s*:\s*List String\)", source, re.S)
    require(m, f"Kernel/ApplicationDispatchAdmission.lean {definition}: shape not recognised")
    return re.findall(r'"([^"]*)"', m[1])

def lean_consent_frames(root):
    """The frame numbers Host/ClientConsentCore.lean dispatches on (match arms, comparisons, ranges)."""
    source = masked((root / LEAN_CONSENT).read_text(), "lean")
    found = {int(n) for n in re.findall(r"\|\s*(2[2-3]\d)\s*=>", source)}
    found |= {int(n) for n in re.findall(r"operation\s*==\s*(2[2-3]\d)\b", source)}
    for a, b in re.findall(r"operation\s*≥\s*(2[2-3]\d)\s*&&\s*operation\s*≤\s*(2[2-3]\d)", source):
        found |= set(range(int(a), int(b) + 1))
    return found

LEAN_HEADERS = Path("Kernel/ApplicationDispatchAdmission.lean")
# The Lean body the generated referer_value_ok mirrors byte for byte (47 = '/', 92 = '\\').
LEAN_REFERER = "def refererValueOk (value : List UInt8) : Bool :=\n  value.head? == some 47 && (value.drop 1).head? != some 47 && !value.contains 92\n"
LEAN_CONSENT = Path("Host/ClientConsentCore.lean")
HOST_MAIN = Path("Host/Main.lean")
TRANSPORT = Path("native/resource-client/src/transport.rs")

def inputs(root, data):
    """Every path `check` reads, relative to root: the one list a copy of the tree must carry."""
    paths = {REGISTRY, GENERATED, GENERATED_LEAN, LEAN_HEADERS, LEAN_CONSENT, HOST_MAIN, TRANSPORT, Path("Effects/Revival/HostedDav.lean")}
    paths.update(Path(binding["path"]) for binding in data["client_constants"])
    paths.update(f.relative_to(root) for crate in WIRE_CRATES for f in (root / "native" / crate).rglob("*.rs"))
    return paths

def check(root, check_generated=True):
    data, ids = load(root)
    symbols = {e["symbol"]: e["code"] for e in ids.values()}
    receivers = host_receivers((root / HOST_MAIN).read_text())
    rust = (root / TRANSPORT).read_text()
    public = rust_routes(rust, "allowed_operation", symbols)
    private = rust_routes(rust, "allowed_operator_operation", symbols)
    active = {code for code, entry in ids.items() if entry["status"] == "active"}
    require(set(receivers) == active, f"Host allocations differ: unregistered/reserved receiving {sorted(set(receivers)-active)}; missing active receivers {sorted(active-set(receivers))}")
    require((public | private) <= active, f"socket routes lack active Host receiver: {sorted((public | private)-active)}")
    for code in sorted(active):
        entry = ids[code]
        require(entry["receiver"] == receivers[code], f"{code} {entry['symbol']}: receiver changed from {entry['receiver']} to {receivers[code]}")
        actual_routes = ["public", "operator"] if code in public else ["operator"] if code in private else []
        require(entry["routes"] == actual_routes, f"{code} {entry['symbol']}: registered routes {entry['routes']} differ from source {actual_routes}")
    for binding in data["client_constants"]:
        source = masked((root / binding["path"]).read_text(), "rust")
        pattern = rf"\bconst {re.escape(binding['constant'])}\s*:\s*u8\s*=\s*([^;]+);"
        matches = re.findall(pattern, source)
        require(len(matches) == 1, f"missing/ambiguous bound client constant {binding['path']}:{binding['constant']}")
        values = selector_codes(matches[0], symbols)
        require(values == [symbols[binding["operation"]]], f"client constant drift: {binding['path']}:{binding['constant']} expected {binding['operation']}")
    require(lean_ordinary_headers(root) == data["ordinary_headers"], "ordinary_headers differ from Kernel/ApplicationDispatchAdmission.lean ordinaryHeaderName (order included)")
    require(LEAN_REFERER in (root / LEAN_HEADERS).read_text(), "Kernel/ApplicationDispatchAdmission.lean refererValueOk changed: update its Rust twin referer_value_ok (generated here) and LEAN_REFERER")
    require(lean_string_list(root, "davMethod") == data["dav_methods"], "dav_methods differ from Kernel/ApplicationDispatchAdmission.lean davMethod (order included)")
    require(lean_string_list(root, "davHeaderName") == data["dav_headers"], "dav_headers differ from Kernel/ApplicationDispatchAdmission.lean davHeaderName (order included)")
    frames = {e["code"] for e in data["consent_frames"]}
    served = lean_consent_frames(root)
    require(served == frames, f"consent frames: Host/ClientConsentCore.lean serves unregistered {sorted(served - frames)}; registered but not served {sorted(frames - served)}")
    literals, unregistered = rust_literals(root, data)
    require(not unregistered, "unregistered consent frame in Rust (register it in consent_frames): " + "; ".join(unregistered[:10]))
    require(not literals, f"{len(literals)} literal Host operation bytes in Rust; name the generated constant (native/host-operations.rs) or mark the line {EXEMPT_MARK}: " + "; ".join(literals[:10]))
    if check_generated:
        require((root / "Effects/Revival/HostedDav.lean").read_text() == generated_hosted_dav(data), "generated hosted DAV vocabulary drift")
        require((root / GENERATED).read_text() == generated(data), "generated request constants drift; run scripts/host-operations.py generate")
        require((root / GENERATED_LEAN).read_text() == generated_lean(data), "generated Lean operation tables drift; run scripts/host-operations.py generate")
    return {"active": len(active), "reserved": len(ids)-len(active), "public": len(public), "operatorOnly": len(private-public), "hostOnly": sorted(active-(public|private)), "clientConstants": len(data["client_constants"]), "consentFrames": len(frames), "ordinaryHeaders": len(data["ordinary_headers"])}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("command", choices=["check", "generate"])
    args = parser.parse_args()
    if args.command == "generate":
        data, _ = load(args.root)
        target = args.root / GENERATED
        target.parent.mkdir(parents=True, exist_ok=True)
        temporary = target.with_name(target.name + f".tmp.{os.getpid()}")
        temporary.write_text(generated(data))
        temporary.replace(target)
        (args.root / "Effects/Revival/HostedDav.lean").write_text(generated_hosted_dav(data))
        lean_target = args.root / GENERATED_LEAN
        temporary = lean_target.with_name(lean_target.name + f".tmp.{os.getpid()}")
        temporary.write_text(generated_lean(data))
        temporary.replace(lean_target)
    result = check(args.root)
    print("host-operations: " + json.dumps(result, sort_keys=True))

if __name__ == "__main__":
    try:
        main()
    except (Invalid, OSError, json.JSONDecodeError) as error:
        print(f"host-operations: FAIL: {error}", file=sys.stderr)
        sys.exit(1)
