#!/usr/bin/env python3
"""Red proofs for the gate's verdict, missing evidence, and CPU resolution."""
import math
import os
import subprocess
import sys
import threading
import time
import unittest
from flatness import assess, failure_prefix, finish, BrokenRun, ProcessCPU, child_pids
from pathlib import Path
from tempfile import TemporaryDirectory


class FlatnessTest(unittest.TestCase):
    def rows(self, cost):
        return [dict(operation=i, history_size=i+2, submit_cpu_ms=cost(i)) for i in range(1, 1001)]

    def verdict(self, cost):
        return assess(self.rows(cost), 1000, 10, ('submit_cpu_ms',))['verdict']

    @unittest.skipUnless(sys.platform.startswith('linux'), 'requires procfs')
    def test_worker_cpu_and_worker_children(self):
        with TemporaryDirectory() as directory:
            pid_file = Path(directory) / 'service.pid'
            pid_file.write_text(str(os.getpid()))
            cpu = ProcessCPU(pid_file)
            before = cpu.read()
            child = []

            def work():
                deadline = time.thread_time() + 0.04
                while time.thread_time() < deadline:
                    pass
                with subprocess.Popen([sys.executable, '-c', 'import sys; sys.stdin.read()'],
                                      stdin=subprocess.PIPE) as proc:
                    child.append(proc.pid in child_pids(os.getpid()))
                    proc.communicate()

            worker = threading.Thread(target=work)
            worker.start()
            worker.join()
            self.assertEqual(child, [True])
            self.assertGreaterEqual(cpu.read() - before, 35)

    def test_constant_passes(self):
        self.assertEqual(self.verdict(lambda _: 100), 'PASS')

    def test_logarithmic_passes(self):
        # Windows contain different history sizes; add the fixed dispatch cost.
        self.assertEqual(self.verdict(lambda n: 100 + math.log2(n)), 'PASS')

    def test_pure_logarithmic_passes(self):
        self.assertEqual(self.verdict(lambda n: 100*math.log2(n+2)), 'PASS')

    def test_static_history_refuses(self):
        rows = self.rows(lambda _: 100)
        for row in rows:
            row['history_size'] = 5
        with self.assertRaises(BrokenRun):
            assess(rows, 1000, 10, ('submit_cpu_ms',))

    def test_linear_fails(self):
        self.assertEqual(self.verdict(lambda n: 10*n), 'FAIL')

    def test_missing_and_duplicate_samples_refuse(self):
        rows = self.rows(lambda _: 100)
        for bad in (rows[:-1], rows[:400] + [rows[398]] + rows[401:]):
            with self.assertRaises(BrokenRun):
                assess(bad, 1000, 10, ('submit_cpu_ms',))

    def test_invalid_cost_refuses(self):
        for value in (float('nan'), float('inf'), -1, 0, 0.001):
            with self.subTest(value=value), self.assertRaises(BrokenRun):
                self.verdict(lambda _: value)

    def test_bad_windows_refuse(self):
        for n, lo in ((1000, 1), (1000, 0), (10, 10), (1000, -1)):
            with self.subTest(n=n, lo=lo), self.assertRaises(BrokenRun):
                assess([], n, lo, ('submit_cpu_ms',))

    def test_early_failure_requires_a_completed_window(self):
        rows = self.rows(lambda n: 10*n)
        self.assertFalse(failure_prefix(rows[:99], 1000, 10, ('submit_cpu_ms',)))
        self.assertTrue(failure_prefix(rows[:100], 1000, 10, ('submit_cpu_ms',)))
        self.assertFalse(failure_prefix(rows[:101], 1000, 10, ('submit_cpu_ms',)))
        self.assertFalse(failure_prefix(rows, 1000, 10, ('submit_cpu_ms',)))
        self.assertFalse(failure_prefix(self.rows(lambda _: 100)[:100], 1000, 10,
                                        ('submit_cpu_ms',)))

    def test_incomplete_pass_cannot_publish(self):
        with TemporaryDirectory() as directory:
            with self.assertRaises(BrokenRun):
                finish(directory, self.rows(lambda _: 100)[:100], 100, 10,
                       ('submit_cpu_ms',), requested_n=1000)
            self.assertFalse((Path(directory) / 'result.json').exists())

    def test_every_required_metric_gates(self):
        rows = self.rows(lambda _: 100)
        for r in rows:
            r['get_wall_ms'] = 10 * r['operation']
        self.assertEqual(assess(rows, 1000, 10, ('submit_cpu_ms', 'get_wall_ms'))['verdict'], 'FAIL')


if __name__ == '__main__':
    unittest.main()
