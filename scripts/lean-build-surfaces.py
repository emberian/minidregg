#!/usr/bin/env python3
"""Generate the explicit compile targets (SimplexQualification.lean, ResearchWip.lean) and the build
surface report.

The report (which module is on the default surface, which is authored research, which are program
roots) is a BUILD OUTPUT, written to build-logs/lean-build-surfaces.json and never tracked: it was a
hash-pinned inventory (protocol/lean-build-surfaces.json) whose every red was "source drift" from an
ordinary edit, and 65 re-pin commits since 10-01 existed only to feed it. What stays checked is what
the generator EMITS into the tree: every emitted target file must be tracked by git and equal to what
the generator writes now (a new untracked emitted file, or a stale one, is red).

  generate   write the emitted targets into the tree, and the report
  check      generate into a scratch dir; RED unless every emitted file is tracked and identical; the report
  json       print the report (consumers: check-build-closure.sh)
  research   lake build ResearchWip + the program roots (opt-in)

This is a source/build graph report. It never promotes an owner's report to a compiler result, a
semantic theorem, or native qualification.
"""
import argparse
import hashlib
import json
import re
import subprocess
import sys
import tempfile
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
        "Kernel.GenericSimplexJumpSafety",
        "Kernel.GenericSimplexReceiverSafety",
        "Verify.GenericSimplexJumpControls",
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
    tops = {"Theory", "Pred", "Kernel", "Compiler", "Assurance", "Effects", "Selvage", "Host", "Verify", "Fixtures"}
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


EMITTED = [group + ".lean" for group in GROUPS] + ["ResearchWip.lean"]


def build(root, out=None):
    """The report; the emitted target files are written under `out` (default: the tree)."""
    out = root if out is None else out
    for group, roots in GROUPS.items():
        for module in roots:
            if not (root / (module.replace(".", "/") + ".lean")).exists():
                raise ValueError("Missing qualification source: " + module)
        (out / (group + ".lean")).write_text(
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
    (out / "ResearchWip.lean").write_text(
        "/- Opt-in authored research compilation. This target may fail; it is\n"
        "excluded from the default qualification gate. Executable roots are listed\n"
        "separately in protocol/lean-build-surfaces.json to avoid main collisions. -/\n" +
        "".join("import " + m + "\n" for m in research))
    modules = source_modules(root)
    inventory = [{"module": name, "path": str(path.relative_to(root)),
                  "surface": "default" if name in default else "authored-research"}
                 for name, path in sorted(modules.items())]
    return {"schema": "minidregg-lean-build-surfaces-v2",
            "meaning": "Declared compile coverage (a build output, not a pin); no aggregate compiler PASS or native qualification is implied.",
            "qualificationTargets": GROUPS,
            "optInTargets": ["ResearchWip"],
            "programRoots": programs,
            "modules": inventory}


def tracked(root, rel):
    return subprocess.run(["git", "ls-files", "--error-unmatch", "--", rel], cwd=root,
                          stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode == 0


def emitted_problems(root, scratch, names):
    """Every emitted file must be tracked and byte-equal to what the generator writes now."""
    problems = []
    for rel in names:
        fresh = (scratch / rel).read_bytes()
        if not tracked(root, rel):
            problems.append(f"emitted target {rel} is not tracked by git (git add it)")
        elif not (root / rel).is_file() or (root / rel).read_bytes() != fresh:
            problems.append(f"emitted target {rel} is stale (run `python3 scripts/lean-build-surfaces.py generate`)")
    return problems


def report(root, data):
    out = root / "build-logs"
    out.mkdir(exist_ok=True)
    (out / "lean-build-surfaces.json").write_text(json.dumps(data, indent=2) + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("mode", choices=["generate", "check", "json", "research"])
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent)
    args = parser.parse_args(); root = args.root.resolve()
    if args.mode == "generate":
        data = build(root); report(root, data)
        print(f"build-surfaces: {len(data['modules'])} source modules; emitted {', '.join(EMITTED)}; report build-logs/lean-build-surfaces.json")
        return
    with tempfile.TemporaryDirectory() as d:
        scratch = Path(d)
        data = build(root, scratch)
        if args.mode == "json":
            print(json.dumps(data, indent=2)); return
        if args.mode == "research":
            subprocess.run(["lake", "build", "ResearchWip"] + data["programRoots"], cwd=root, check=True); return
        # self-test, every run: an emitted file git does not track is red by name
        (scratch / "SelfTestUntracked.lean").write_text("-- plant\n")
        plant = emitted_problems(root, scratch, ["SelfTestUntracked.lean"])
        if not plant or "not tracked" not in plant[0]:
            raise SystemExit("build-surfaces: instrument: an untracked emitted plant was not refused")
        problems = emitted_problems(root, scratch, EMITTED)
    report(root, data)
    for p in problems:
        print("build-surfaces: RED " + p)
    if problems:
        raise SystemExit(1)
    print(f"build-surfaces: PASS: {len(EMITTED)} emitted targets tracked and current ({len(data['modules'])} modules classified; "
          f"self-test: an untracked emitted file is refused); compiler results are separate")


if __name__ == "__main__":
    main()
