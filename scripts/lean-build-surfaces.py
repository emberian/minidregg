#!/usr/bin/env python3
"""Generate explicit compile targets and a hash-pinned source inventory.

This is a source/build graph report. It never promotes an owner's report to a
compiler result, a semantic theorem, or native qualification.
"""
import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from lean_imports import header_imports

GROUPS = {
    "SimplexQualification": [
        "Kernel.GeneralSimplexReachability",
        "Kernel.GenericSimplexCausal",
        "Kernel.GenericSimplexPreparedHistory",
        "Kernel.GenericSimplexEmissionSupport",
        "Kernel.GenericSimplexEngineSafety",
        "Kernel.GenericSimplexObservationSafety",
        "Kernel.GenericSimplexReceiverSafety",
    ],
}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def source_modules(root):
    files = subprocess.check_output(
        ["git", "ls-files", "-z", "--", "*.lean"], cwd=root
    ).decode().split("\0")
    # During an authorized source-first publication, include staged and new
    # library source as well. Exclude build output and standalone scripts.
    tops = {"Theory", "Pred", "Kernel", "Compiler", "Assurance", "Effects", "Selvage", "Host", "Verify"}
    for top in tops:
        files.extend(str(p.relative_to(root)) for p in (root / top).glob("**/*.lean"))
    files.extend(name + ".lean" for name in GROUPS)
    files.append("ResearchWip.lean")
    return {p[:-5].replace("/", "."): root / p for p in sorted(set(files))
            if p and (root / p).is_file() and
            (p.split("/")[0].removesuffix(".lean") in tops or "/" not in p)}


def imports(path):
    return header_imports(path.read_text())


def closure(modules, roots):
    seen, stack = set(), list(roots)
    while stack:
        name = stack.pop()
        if name.startswith("Minidregg.") and name[10:] in modules:
            name = name[10:]
        if name in seen or name not in modules:
            continue
        seen.add(name)
        stack.extend(imports(modules[name]))
    return seen


def build(root):
    for group, roots in GROUPS.items():
        for module in roots:
            if not (root / (module.replace(".", "/") + ".lean")).exists():
                raise ValueError("Missing qualification source: " + module)
        (root / (group + ".lean")).write_text(
            "/- Explicit compile target. Aggregate compilation and semantic/native\n"
            "qualification are separate. See docs/LEAN-QUALIFICATION.md. -/\n" +
            "".join("import " + module + "\n" for module in roots))
    modules = source_modules(root)
    lake = (root / "lakefile.toml").read_text()
    libs = re.findall(r'^\[\[lean_lib\]\]\s*\nname\s*=\s*"([^"]+)"', lake, re.M)
    exe = re.findall(r'^\[\[lean_exe\]\]\s*\nname\s*=\s*"[^"]+"\s*\nroot\s*=\s*"([^"]+)"', lake, re.M)
    default = closure(modules, [m for m in libs if m != "ResearchWip"] + exe)
    unrooted = set(modules) - default - {"ResearchWip"}
    programs = sorted(m for m in unrooted if re.search(r"^def main(?:\s|\(|:)", modules[m].read_text(), re.M))
    research = sorted(unrooted - set(programs))
    (root / "ResearchWip.lean").write_text(
        "/- Opt-in authored research compilation. This target may fail; it is\n"
        "excluded from the default qualification gate. Executable roots are listed\n"
        "separately in protocol/lean-build-surfaces.json to avoid main collisions. -/\n" +
        "".join("import " + m + "\n" for m in research))
    modules = source_modules(root)
    reports = json.loads((root / "docs/construction/source-intake-20261003.json").read_text())["files"]
    by_path = {f["path"]: f for f in reports}
    inventory = []
    for name, path in sorted(modules.items()):
        rel = str(path.relative_to(root)); sha = digest(path.read_bytes()); report = by_path.get(rel)
        row = {"module": name, "path": rel, "sha256": sha,
               "surface": "default" if name in default else "authored-research"}
        if report and report["sha256"] == sha:
            row["ownerReportedStatus"] = report.get("qualification", "unspecified")
        else:
            row["ownerReportedStatus"] = "No matching owner source report"
        inventory.append(row)
    return {"schema": "minidregg-lean-build-surfaces-v1",
            "meaning": "Declared compile coverage and source hashes; no aggregate compiler PASS or native qualification is implied.",
            "qualificationTargets": GROUPS,
            "optInTargets": ["ResearchWip"],
            "programRoots": programs,
            "modules": inventory}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=["generate", "check", "research"])
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent)
    args = parser.parse_args(); root = args.root.resolve()
    path = root / "protocol/lean-build-surfaces.json"
    if args.mode == "generate":
        data = build(root); path.write_text(json.dumps(data, indent=2) + "\n")
        print(f"build-surfaces: {len(data['modules'])} source modules; explicit qualification and opt-in research targets generated")
    else:
        data = json.loads(path.read_text())
        for row in data["modules"]:
            source = root / row["path"]
            if not source.is_file() or digest(source.read_bytes()) != row["sha256"]:
                raise SystemExit("build-surfaces: source drift: " + row["path"])
        declared = {row["module"] for row in data["modules"]}
        missing = set(source_modules(root)) - declared
        if missing:
            raise SystemExit("build-surfaces: unclassified source: " + ", ".join(sorted(missing)))
        if args.mode == "research":
            subprocess.run(["lake", "build", "ResearchWip"] + data["programRoots"], cwd=root, check=True)
        else:
            print(f"build-surfaces: source pins/classification PASS ({len(declared)} modules); compiler results are separate")


if __name__ == "__main__":
    main()
