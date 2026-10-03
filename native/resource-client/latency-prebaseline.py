#!/usr/bin/env python3
"""Pre-room whole-action timing baseline on the supplied world (read-only member actions).

Adapts latency-same-store.py beside this file, whose own
`baseline` mode needs a shared room reference and so cannot run before any room exists.
This reuses that adapter's Probe unchanged (operator instance + live Host identity checks,
SSH action wall time, Host CPU delta, retained batch coordinates) and only supplies the
action list a member has before rooms: the forced-SSH session binding, reference
discovery, and signed reads of the member's own account and of the factory object.
Every row also records /proc/loadavg, because hbox is shared and is not kept quiet.
It constructs, restarts and writes nothing in the world.
"""
import argparse
import importlib.util
import json
from pathlib import Path
import statistics
import time

ADAPTER = Path(__file__).resolve().with_name('latency-same-store.py')
loader = importlib.util.spec_from_file_location('latency_same_store', ADAPTER)
latency = importlib.util.module_from_spec(loader); loader.loader.exec_module(latency)


def load():
    return [float(value) for value in Path('/proc/loadavg').read_text().split()[:3]]


class PreRoom(latency.Probe):
    def call(self, label, line):
        before = load()
        text = super().call(label, line)
        self.rows[-1].update(loadavgBefore=before, loadavgAfter=load(), bytes=len(text))
        latency.save(self.output / 'timings.json', self.rows)
        return text

    def prebaseline(self, samples):
        actions = [('session', 'whoami'), ('discovery', 'refs'), ('signed-read-account', 'read account'),
                   ('signed-read-factory', 'read factory')]
        for index in range(samples):
            for label, line in actions:
                self.call(f'{label}-{index + 1}', line)
        summary = {}
        for label, line in actions:
            rows = [row for row in self.rows if row['id'].rsplit('-', 1)[0] == label]
            seconds = [row['seconds'] for row in rows]
            summary[label] = {'command': line, 'samples': seconds, 'medianSeconds': statistics.median(seconds),
                              'worstSeconds': max(seconds), 'hostCpuSeconds': [row['hostCpuSeconds'] for row in rows],
                              'signedBatches': [len(row['batches']) for row in rows]}
        return summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('spec', 'output', 'member', 'expected-manifest-sha'):
        parser.add_argument('--' + name, required=True)
    parser.add_argument('--host-pid', required=True, type=int)
    parser.add_argument('--samples', type=int, default=3)
    args = parser.parse_args()
    args.mode = 'pre-room-baseline'
    started, wall = load(), time.time()
    probe = PreRoom(args)
    try:
        summary = probe.prebaseline(args.samples)
    except BaseException as exc:
        latency.save(probe.output / 'probe-failure.json', {'error': str(exc), 'identity': probe.j.identity,
                                                          'effectRetry': 'none; read-only actions'})
        raise
    result = {'protocol': 'mini-pre-room-latency-baseline-v1', 'identity': probe.j.identity, 'member': args.member,
              'adapter': {'path': str(ADAPTER), 'sha256': latency.hashlib.sha256(ADAPTER.read_bytes()).hexdigest()},
              'scope': 'whole forced-SSH member action wall time before any room or concurrent write; hbox not quiet, loadavg recorded per row',
              'loadavgStart': started, 'loadavgEnd': load(), 'wallSeconds': time.time() - wall, 'actions': summary,
              'timings': str(probe.output / 'timings.json')}
    latency.save(probe.output / 'baseline-result.json', result)
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
