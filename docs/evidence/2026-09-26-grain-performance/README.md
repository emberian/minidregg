# Grain host observation latency on an exact copied Store

On 2026-09-26, a read-only SQLite `backup` captured the private grain run's
Store as `/tmp/mga-b-043507-perf-copy/forward-link.sqlite3` (SHA-256
`0fcb85ad703099e533ab8dee14a7deb5d1360985d06897c4de4c37e63d9becf2`).
The active Store and socket were never used by this measurement. Both hosts
read the same copied Store and the same already signed resource query from
`query-0000000000000021` (challenge height 22). The exact intent and signed
observation SHA-256 hashes were respectively
`14636c9b26f3351e273ab0f7671bd9138b516758abaada8cc063b999150d54df`
and `f87cf4f785b90279c3cea2d714a98478b8a06afb6d900e8e93733c170fddf302`.

| Host | Cold open plus first describe | Warm describe | Challenge (3 trials) | Signed query (3 trials) |
| --- | ---: | ---: | ---: | ---: |
| Before, SHA `c2a1fd3699338f28eaf1d076b53cbd1bf27b4438b857b0482666205b334a394c` | 124.389 s | 0.828 s | 7.742, 7.947, 8.061 s | 17.780, 17.795, 17.934 s |
| Boundary-sharing/session refresh, SHA `b9ff9832b13ad67124e753ab52122732bfe9b795653e2ba64c1e0f35b051ee8a` | 117.031 s | 0.031 s | 2.422, 2.426, 2.421 s | 5.472, 5.505, 5.511 s |

Every challenge response and signed query view was byte-identical between
hosts and to the recorded grain-run artifact. Challenge SHA-256 (including
stdio opcode) was `46e1a57ffe5fee4ec17dc868b4b396eb9586953990b43e71689c69d58f5131d0`;
view SHA-256 was `76b0d382d9fa42482d474f27d48a70da9a20d45c640cd02576475ee6b3e6bed9`.
The [old](old-host.jsonl) and [new](new-host.jsonl) JSONL records contain each
trial; [the driver](bench-grain-observation.py) shows the stdio framing and
byte comparison.

Another active host used roughly one full CPU core during both sequential
runs. The paired warm timings were stable but are contended wall-clock
measurements. The new host contains only the `NativeObservationController`
boundary-sharing and `NativeHostSession` exact-byte reread changes; it does
not contain the later `DurableReceiverIO` CAS readback optimization. Cold
semantic replay remains around two minutes and is a separate startup cost.

The existing `scripts/overnight-tests/replay-poison.sh` also passed against
the new host on a fresh real SQLite fixture. Replacing its live image with a
valid rollback closed the session at entry 1; replacing it with a valid
same-height fork closed it at entry 2. A subsequent frame remained closed in
both cases. The local run is
`/tmp/minidregg-overnight-20260926/poison-next`.
