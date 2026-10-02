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
    require(set(data) == {"format", "operations", "response_markers", "client_constants"}, "unknown registry fields")
    ids, symbols = {}, set()
    for entry in data["operations"]:
        require(set(entry) == {"code", "symbol", "status", "routes", "owner", "purpose", "receiver"}, f"invalid operation fields: {entry}")
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
        ids[code] = entry
        symbols.add(symbol)
    responses = set()
    for entry in data["response_markers"]:
        require(set(entry) == {"code", "purpose", "request_reserved"} and type(entry["code"]) is int and type(entry["request_reserved"]) is bool, "invalid response marker")
        require(0 <= entry["code"] <= 255 and entry["code"] not in responses, "duplicate/invalid response marker")
        require(not entry["request_reserved"] or entry["code"] not in ids, f"request collides with reserved response marker: {entry['code']}")
        responses.add(entry["code"])
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
        if language == "rust":
            raw = re.match(r'(?:br|r)(#*)"', source[i:])
            if raw:
                end_marker = '"' + raw[1]
                end = source.find(end_marker, i + raw.end())
                require(end >= 0, "unclosed Rust raw string")
                end += len(end_marker); blank(i, end); i = end; continue
            character = re.match(r"'(?:[^'\\\n]|\\(?:x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]+\}|.))'", source[i:])
            if character:
                end = i + character.end(); blank(i, end); i = end; continue
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
        symbol = re.fullmatch(r"(?:crate::)?host_operations::([A-Z][A-Z0-9_]*)", part)
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

def generated(data):
    lines = ["// Generated by scripts/host-operations.py generate; edit protocol/host-operations.json.",
             "// Request byte allocations only. No payload codecs or admission rules live here.",
             "#![allow(dead_code)]", ""]
    for entry in sorted(data["operations"], key=lambda e: e["code"]):
        lines += [f"// {entry['status']}; {','.join(entry['routes']) or 'Host stdio only'}; owner: {entry['owner']}",
                  f"pub const {entry['symbol']}: u8 = {entry['code']};"]
    return "\n".join(lines) + "\n"

def check(root, check_generated=True):
    data, ids = load(root)
    symbols = {e["symbol"]: e["code"] for e in ids.values()}
    receivers = host_receivers((root / "Host/Main.lean").read_text())
    rust = (root / "native/resource-client/src/transport.rs").read_text()
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
    if check_generated:
        require((root / GENERATED).read_text() == generated(data), "generated request constants drift; run scripts/host-operations.py generate")
    return {"active": len(active), "reserved": len(ids)-len(active), "public": len(public), "operatorOnly": len(private-public), "hostOnly": sorted(active-(public|private)), "clientConstants": len(data["client_constants"])}

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
    result = check(args.root)
    print("host-operations: " + json.dumps(result, sort_keys=True))

if __name__ == "__main__":
    try:
        main()
    except (Invalid, OSError, json.JSONDecodeError) as error:
        print(f"host-operations: FAIL: {error}", file=sys.stderr)
        sys.exit(1)
