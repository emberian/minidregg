#!/usr/bin/env python3
"""Exercise build-native-host.sh's seated Lean wrapper (the real heredoc text) without invoking Lean.

16 concurrent "compilers" over 3 host-wide seats: at most 3 run at once and 3 do; every START has
its END; every seat directory is gone afterwards. Occupied seats with MINIDREGG_LEAN_SEAT_WAIT=0:
the wrapper refuses with 75 and leaves the owners' directories intact. A TERM delivered to the
wrapper while its compiler runs does not release the seat before the compiler exits.
"""
import os
from pathlib import Path
import signal
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[2]
SOURCE = (ROOT / "scripts/build-native-host.sh").read_text()
WRAPPER = SOURCE.split('cat > "$wrapper_root/bin/lean" <<\'EOF\'\n', 1)[1].split("\nEOF\n", 1)[0] + "\n"
RUSAGE = SOURCE.split('cat > "$wrapper_root/lean-rusage.py" <<\'EOF\'\n', 1)[1].split("\nEOF\n", 1)[0] + "\n"

with tempfile.TemporaryDirectory(prefix="mini-native-seats-") as temporary:
    root = Path(temporary)
    wrapper = root / "lean"
    wrapper.write_text(WRAPPER)
    (root / "lean-rusage.py").write_text(RUSAGE)
    fake = root / "fake-lean"
    fake.write_text("#!/bin/sh\nsleep 0.3\n")
    fake.chmod(0o755)
    seats = root / "seats"
    seats.mkdir()
    log = root / "wrapper.tsv"
    env = os.environ | {
        "MINIDREGG_REAL_LEAN": str(fake),
        "MINIDREGG_LEAN_SEAT_ROOT": str(seats),
        "MINIDREGG_LEAN_SEATS": "3",
        "MINIDREGG_LEAN_SEAT_WAIT": "60",
        "MINIDREGG_LEAN_WRAPPER_LOG": str(log),
        "MINIDREGG_LEAN_BUILD_ROOT": str(root),
        "LEAN_NUM_THREADS": "2",
        "MINIDREGG_LEAN_RUSAGE": str(root / "lean-rusage.py"),
    }
    workers = [subprocess.Popen(["bash", str(wrapper), f"M{i}.lean"], env=env) for i in range(16)]
    assert all(worker.wait(timeout=120) == 0 for worker in workers)
    active, maximum, starts = set(), 0, 0
    rss = []
    for line in log.read_text().splitlines():
        event, _, pid, *_ = line.split("\t")
        if event == "RSS":
            _, _, source, wall, maxrss, rc = line.split("\t")
            assert source.endswith(".lean") and float(wall) >= 0.3 and int(maxrss) > 0 and rc == "0", line
            rss.append(source)
            continue
        if event == "START":
            assert pid not in active
            active.add(pid)
            starts += 1
            maximum = max(maximum, len(active))
        else:
            assert event == "END" and pid in active, line
            active.remove(pid)
    assert starts == 16 and not active, (starts, active)
    assert maximum == 3, maximum
    assert sorted(rss) == sorted(f"M{i}.lean" for i in range(16)), rss
    assert not list(seats.iterdir()), list(seats.iterdir())
    print("PASS: 16 compiler jobs over 3 seats, at most and at least 3 at once, balanced, seats released, one RSS line each (wall, maxrss)")

    # occupied seats, no wait: refuse 75, owners untouched
    for number in (1, 2, 3):
        seat = seats / f"lean-seat-{number}"
        seat.mkdir()
        (seat / "owner.txt").write_text("retained owner\n")
    refused = subprocess.run(["bash", str(wrapper), "X.lean"], env=env | {"MINIDREGG_LEAN_SEAT_WAIT": "0"})
    assert refused.returncode == 75, refused.returncode
    assert all((seats / f"lean-seat-{n}/owner.txt").read_text() == "retained owner\n" for n in (1, 2, 3))
    for number in (1, 2, 3):
        (seats / f"lean-seat-{number}/owner.txt").unlink()
        (seats / f"lean-seat-{number}").rmdir()
    print("PASS: occupied seats refuse with 75 at MINIDREGG_LEAN_SEAT_WAIT=0 and stay intact")

    # TERM to the wrapper: the seat outlives the compiler's own exit, never the other way round
    slow = root / "slow-lean"
    slow.write_text("#!/bin/sh\ntrap '' TERM\nsleep 1.5\n")
    slow.chmod(0o755)
    held = subprocess.Popen(["bash", str(wrapper), "S.lean"], env=env | {"MINIDREGG_REAL_LEAN": str(slow)})
    deadline = time.monotonic() + 10
    while not (seats / "lean-seat-1").exists():
        assert time.monotonic() < deadline
        time.sleep(0.02)
    time.sleep(0.2)
    held.send_signal(signal.SIGTERM)
    time.sleep(0.5)
    assert (seats / "lean-seat-1").exists(), "seat released while the compiler still ran"
    held.wait(timeout=10)
    assert not list(seats.iterdir())
    print("PASS: a TERMed wrapper holds its seat until the compiler exits, then releases it")
