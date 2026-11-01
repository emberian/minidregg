"""Shared measurement and verdict code for the law-17 receiving-path gates.

This is a benchmark harness, not a source of Mini admission decisions.
"""
import json
import math
import os
from pathlib import Path
import signal
import statistics
import subprocess
import time


class BrokenRun(RuntimeError):
    pass


def validate_sizes(n, lo):
    if lo < 10 or n < 4 * lo:
        raise BrokenRun('need lo >= 10 and n >= 4 * lo (disjoint measured windows)')


def assess(rows, n, lo, required):
    """Missing, non-finite or below-resolution measurements never count as PASS."""
    validate_sizes(n, lo)
    if len(rows) != n or [r['operation'] for r in rows] != list(range(1, n + 1)):
        raise BrokenRun('incomplete or non-sequential operation samples')
    early = rows[lo // 2:lo]
    late = rows[-lo:]
    if not required:
        raise BrokenRun('no required metrics')
    sizes = [r['history_size'] for r in rows]
    if any(not isinstance(v, int) or v < 2 for v in sizes) or any(
            b <= a for a, b in zip(sizes, sizes[1:])):
        raise BrokenRun('history sizes must strictly increase')
    # Match the mean-cost windows: a pure logarithmic cost must pass without
    # granting the larger operation-count bound to a world with a long bootstrap.
    small_log = statistics.mean(math.log2(r['history_size']) for r in early)
    large_log = statistics.mean(math.log2(r['history_size']) for r in late)
    bound = max(1.5, large_log / small_log)
    results = {}
    for name in required:
        values = [r[name] for r in rows]
        if any(not math.isfinite(v) or v < 0 for v in values):
            raise BrokenRun(f'{name}: invalid measurement')
        small = statistics.mean(r[name] for r in early)
        large = statistics.mean(r[name] for r in late)
        # Sub-10ms operations use nanosecond /proc/<pid>/schedstat accounting,
        # so require at least 1.0 ms across the early window.
        resolution = 1.0 if name.endswith('_cpu_ms') else 0
        if small <= 0 or sum(r[name] for r in early) < resolution:
            raise BrokenRun(f'{name}: early window below measurement resolution; increase --lo')
        ratio = large / small
        results[name] = dict(early=small, late=large, ratio=ratio, bound=bound,
                             verdict='PASS' if ratio <= bound else 'FAIL')
    return dict(verdict='PASS' if all(r['verdict'] == 'PASS' for r in results.values()) else 'FAIL',
                n=n, lo=lo, metrics=results)


def proc_stat(pid):
    fields = Path(f'/proc/{pid}/stat').read_text().rsplit(')', 1)[1].split()
    tck = os.sysconf('SC_CLK_TCK')
    try:
        # High-resolution nanosecond scheduler runtime for this process.
        self_ms = int(Path(f'/proc/{pid}/schedstat').read_text().split()[0]) / 1e6
        reaped_ms = (int(fields[13]) + int(fields[14])) * 1000.0 / tck
        return int(fields[19]), self_ms + reaped_ms
    except OSError:
        return int(fields[19]), sum(int(x) for x in fields[11:15]) * 1000.0 / tck


class ProcessCPU:
    """An explicitly selected service and its descendants, with PID reuse detection."""
    def __init__(self, pid_file):
        self.pid_file = Path(pid_file)
        self.pid = int(self.pid_file.read_text())
        self.start, _ = proc_stat(self.pid)

    def read(self):
        if int(self.pid_file.read_text()) != self.pid or proc_stat(self.pid)[0] != self.start:
            raise BrokenRun('measured service restarted or its PID was reused')
        def cpu_ms(pid):
            _, total = proc_stat(pid)
            children = Path(f'/proc/{pid}/task/{pid}/children').read_text().split()
            for child in children:
                try:
                    total += cpu_ms(int(child))
                except FileNotFoundError:
                    # The service's waited-for time accounts for a reaped helper.
                    pass
            return total
        return cpu_ms(self.pid)

    def stop(self):
        try:
            if int(self.pid_file.read_text()) == self.pid and proc_stat(self.pid)[0] == self.start:
                os.kill(self.pid, signal.SIGTERM)
        except ProcessLookupError:
            pass
        except FileNotFoundError:
            pass


class Commands:
    def __init__(self, transcript):
        self.transcript = Path(transcript)
        self.transcript.mkdir(parents=True, exist_ok=True)

    def run(self, tag, *args, timeout=900):
        child = subprocess.Popen([str(a) for a in args], stdout=subprocess.PIPE,
                                 stderr=subprocess.PIPE)
        pid_file = self.transcript / (tag + '.pid')
        pid_file.write_text(str(child.pid) + '\n')
        try:
            out, err = child.communicate(timeout=timeout)
        except subprocess.TimeoutExpired:
            os.kill(int(pid_file.read_text()), signal.SIGTERM)
            out, err = child.communicate(timeout=10)
            (self.transcript / (tag + '.out')).write_bytes(out)
            (self.transcript / (tag + '.err')).write_bytes(err)
            raise BrokenRun(f'{tag}: timed out; see {self.transcript}')
        (self.transcript / (tag + '.out')).write_bytes(out)
        (self.transcript / (tag + '.err')).write_bytes(err)
        if child.returncode:
            raise BrokenRun(f'{tag}: exit {child.returncode}; see {self.transcript / (tag + ".err")}')
        return out.decode()

    def measured(self, cpu, tag, *args):
        before = cpu.read()
        start = time.monotonic_ns()
        output = self.run(tag, *args)
        wall = (time.monotonic_ns() - start) / 1e6
        used = cpu.read() - before
        if used < 0:
            raise BrokenRun(f'{tag}: process CPU accounting moved backwards')
        return output, wall, used


def failure_prefix(rows, requested_n, lo, metrics):
    """A growing-cost candidate need not finish a quadratic 1,000-turn run.

    Check after at least 100 operations (past the first certification), then
    at doubled windows. Only a FAIL may finish early; PASS requires all turns.
    """
    count = len(rows)
    first = max(100, 4 * lo)
    if count >= requested_n or count < first or count % first:
        return False
    multiple = count // first
    if multiple & (multiple - 1):
        return False
    return assess(rows, count, lo, metrics)['verdict'] == 'FAIL'


def finish(root, rows, n, lo, metrics, *, requested_n=None):
    report = assess(rows, n, lo, metrics)
    report['requested_n'] = n if requested_n is None else requested_n
    report['stopped_early'] = report['requested_n'] != n
    if report['stopped_early'] and report['verdict'] != 'FAIL':
        raise BrokenRun('an incomplete run cannot pass')
    (Path(root) / 'result.json').write_text(json.dumps(report, indent=2) + '\n')
    for name, r in report['metrics'].items():
        print(f'FLATNESS {name} early={r["early"]:.3f} late={r["late"]:.3f} '
              f'ratio={r["ratio"]:.3f} bound={r["bound"]:.3f} {r["verdict"]}', flush=True)
    return 0 if report['verdict'] == 'PASS' else 1


def certify(commands, mini, workspace, control, tag):
    output = commands.run(tag, mini, 'checkpoint', '--action', 'certify',
                          '--workspace', workspace, '--control', control, '--min-tail', '1')
    result = json.loads(output)
    if result.get('type') != 'confirmed' or result.get('confirmation') != 'installed':
        raise BrokenRun(f'{tag}: certification did not install: {result.get("type")}')
