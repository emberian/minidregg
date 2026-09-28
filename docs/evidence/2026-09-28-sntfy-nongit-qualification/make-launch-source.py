#!/usr/bin/env python3
"""Project one verified installed SPK manifest into Mini's launch author input."""

import json
import sys
from pathlib import Path


def command(value):
    return {
        "argvHex": [argument.encode("utf-8").hex() for argument in value["argv"]],
        "environHex": [
            {"keyHex": key.encode("utf-8").hex(), "valueHex": item.encode("utf-8").hex()}
            for key, item in value["environ"]
        ],
    }


manifest_path, package_path, output_path = map(Path, sys.argv[1:])
manifest = json.loads(manifest_path.read_text())
source = {
    "packageCanonicalHex": package_path.read_bytes().hex(),
    "createCommands": [command(action["command"]) for action in manifest["actions"]],
    "continueCommand": command(manifest["continue_command"]),
}
output_path.write_text(json.dumps(source, sort_keys=True, indent=2) + "\n")
