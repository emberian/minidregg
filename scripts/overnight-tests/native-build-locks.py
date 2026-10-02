#!/usr/bin/env python3
"""Exercise the actual native builder lock snippets without invoking Lean."""
import os
from pathlib import Path
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[2]
SOURCE = (ROOT / "scripts/build-native-host.sh").read_text()
WRAPPER = SOURCE.split('cat > "$wrapper_root/bin/lean" <<\'EOF\'\n', 1)[1].split("\nEOF", 1)[0]
SEATS = "for seat_number in 1 2; do\n" + SOURCE.split("for seat_number in 1 2; do\n", 1)[1].split("\ndone", 1)[0] + "\ndone\n"

def wait_for(predicate, timeout=10):
    deadline = time.monotonic() + timeout
    while not predicate():
        if time.monotonic() > deadline:
            raise AssertionError("bounded lock test timed out")
        time.sleep(0.01)

with tempfile.TemporaryDirectory(prefix="mini-native-locks-") as temporary:
    root = Path(temporary)
    wrapper = root / "lean"
    wrapper.write_text(WRAPPER)
    fake = root / "fake-lean"
    fake.write_text("#!/bin/sh\nsleep 0.05\n")
    fake.chmod(0o755)
    log = root / "wrapper.tsv"
    env = os.environ | {
        "MINIDREGG_REAL_LEAN": str(fake),
        "MINIDREGG_LEAN_LOCK": str(root / "compiler"),
        "MINIDREGG_LEAN_WRAPPER_LOG": str(log),
        "LEAN_NUM_THREADS": "2",
    }
    workers = [subprocess.Popen(["bash", str(wrapper), str(i)], env=env) for i in range(16)]
    assert all(worker.wait(timeout=10) == 0 for worker in workers)
    active = set()
    maximum = 0
    for line in log.read_text().splitlines():
        event, _, pid, *_ = line.split("\t")
        if event == "START":
            active.add(pid)
            maximum = max(maximum, len(active))
        else:
            assert pid in active
            active.remove(pid)
    assert maximum == 1 and not active, (maximum, active)
    print("PASS: 16 compiler jobs, exactly one active, balanced START/END")

    def seat_round(name, occupied=False):
        seats = root / name
        seats.mkdir()
        if occupied:
            for number in (1, 2):
                seat = seats / f"lean-seat-{number}"
                seat.mkdir()
                (seat / "owner.txt").write_text("retained owner\n")
        script = root / f"{name}.sh"
        script.write_text("""#!/bin/bash
set -eu
seat_root=$1
result=$2
release=$3
root=$4
cycle_dir=$5
seat_dir=""
""" + SEATS + """
printf '%s\\n' "$seat_dir" > "$result"
while [[ ! -e "$release" ]]; do sleep 0.01; done
if [[ -n "$seat_dir" ]]; then
  rm "$seat_dir/owner.txt"
  rmdir "$seat_dir"
fi
""")
        release = root / f"{name}.release"
        results = [root / f"{name}.{i}.result" for i in range(16)]
        evidence = [root / f"{name}.evidence.{i}" for i in range(16)]
        for directory in evidence:
            directory.mkdir()
        workers = [subprocess.Popen(["bash", str(script), str(seats), str(result),
                                    str(release), str(ROOT), str(directory)])
                   for result, directory in zip(results, evidence)]
        try:
            wait_for(lambda: all(result.exists() for result in results))
            winners = [result.read_text().strip() for result in results if result.read_text().strip()]
            assert len(winners) == (0 if occupied else 2), winners
            assert len(set(winners)) == len(winners)
            if occupied:
                assert all((seats / f"lean-seat-{i}/owner.txt").read_text() == "retained owner\n"
                           for i in (1, 2))
        finally:
            release.touch()
            assert all(worker.wait(timeout=10) == 0 for worker in workers)
        if not occupied:
            assert not list(seats.iterdir())
            assert all(not list(directory.iterdir()) for directory in evidence)
    seat_round("contended")
    print("PASS: 16 independent evidence directories, two global seats, exact cleanup")
    seat_round("occupied", occupied=True)
    print("PASS: existing/stale owner directories refuse and remain intact")
