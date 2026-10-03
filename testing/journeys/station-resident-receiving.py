#!/usr/bin/env python3
"""Station-specific consumer of the unchanged native resident receiving journey.

No native platform/authority/payment semantics are implemented here. A distinct
allocated task and actual signed station input document are required. The common
journey performs source birth, current tools, exact custody, paid document output,
signed final delivery and recovery; this layer checks the opaque station reply.
Suggested source calls remain data. Current-authorized source action receiving is
independent and does not follow automatically from successful narration.
"""
import argparse
import hashlib
import json
import pathlib
import subprocess
import sys


def load(path):
    return json.loads(pathlib.Path(path).read_text())


def unique_argument(args, flag):
    positions = [i for i, arg in enumerate(args) if arg == flag]
    if len(positions) != 1 or positions[0] + 1 >= len(args):
        raise ValueError("one explicit " + flag + " required")
    return args[positions[0] + 1]


def verify_station(receiving, expected):
    common = load(receiving / "result.json")
    if common.get("passed") is not True:
        raise ValueError("native resident receiving journey has not passed")
    records = load(receiving / "provider-received.json")
    if not records or len(records) != common.get("providerCalls"):
        raise ValueError("station provider count differs from native receiving")
    replies = []
    for record in records:
        reply = json.loads(record["reply"])
        if set(reply) != {"type", "narrative", "citedInput", "suggestedSourceCall"} or reply["type"] != "station-gm-output-v1":
            raise ValueError("station reply contains an unexpected authority/effect field")
        reads = [row for row in record["body"]["messages"]
                 if row.get("role") == "tool" and row.get("tool_call_id") == "captured-input-read"]
        if len(reads) != 1:
            raise ValueError("one retained actual native input frame required")
        native = json.loads(json.loads(reads[0]["content"])["content"][0]["text"])
        actual = json.loads(native["text"])
        text_hash = hashlib.sha256(native["text"].encode()).hexdigest()
        cited = reply["citedInput"]
        if cited["document"] != native["doc"] or cited["textSha256"] != text_hash or record["nativeInputTextSha256"] != text_hash:
            raise ValueError("station reply differs from its exact native input")
        for key in ("source", "observations"):
            if cited[key] != actual[key] or actual[key] != expected[key]:
                raise ValueError("station source/root citation changed: " + key)
        if reply["narrative"] != actual["narrative"] or reply["suggestedSourceCall"] != actual["suggestion"]:
            raise ValueError("station narration/suggestion differs from its authored input")
        replies.append(record["reply"])
    return {"type": "station-resident-citation-check-v1", "providerCalls": len(records),
            "nativeResidentChecks": common["checks"], "citedSource": expected["source"],
            "narrationReceived": True, "worldSourceActionsInstalled": False,
            "scope": "scripted local provider; no paid model qualification"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--station-input", required=True, help="authored exact source/root/narration/suggestion input")
    parser.add_argument("--receiving-directory", required=True, help="allocated task's common receiving directory")
    parser.add_argument("--common-runner-sha256", required=True, help="exact frozen common runner source selected by its owner")
    parser.add_argument("--verify-only", action="store_true")
    args, forwarded = parser.parse_known_args()
    if forwarded and forwarded[0] == "--":
        forwarded = forwarded[1:]
    own = pathlib.Path(__file__).resolve().parent
    runner = own / "shared-resident-useful-work.py"
    if hashlib.sha256(runner.read_bytes()).hexdigest() != args.common_runner_sha256:
        raise ValueError("common resident runner source differs from selected source")
    receiving = pathlib.Path(args.receiving_directory).resolve()
    base = pathlib.Path(unique_argument(forwarded, "--base")).resolve()
    task = unique_argument(forwarded, "--task")
    if not task.isdecimal() or receiving != base / "var/lib/mini/controllers" / task / "receiving":
        raise ValueError("station receiving path differs from explicitly allocated native task")
    if any(arg in ("--fixture-acp", "--fixture-provider") for arg in forwarded):
        raise ValueError("this consumer fixes its explicit ACP/provider source")
    if not args.verify_only:
        status = subprocess.run([sys.executable, str(runner), *forwarded,
            "--fixture-acp", str(own / "shared-resident-fixture-acp"),
            "--fixture-provider", str(own / "station-resident-fixture-provider.py")]).returncode
        if status:
            return status
        if not (receiving / "result.json").exists():
            print("STATION SETUP ONLY: native resident run not yet complete")
            return 0
    report = verify_station(receiving, load(args.station_input))
    print(json.dumps(report, indent=2))
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (ValueError, KeyError, OSError, TypeError) as error:
        print("STATION RESIDENT REFUSED: " + str(error), file=sys.stderr)
        sys.exit(1)
