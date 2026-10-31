# Whole-store lifecycle sweep

`store-sweep.sh` visits every entry of the public Sandstorm index, in index order, with
no app-specific requests. It uses `grain-journey.sh`'s market coordinates j..p (seven per
world), the owner `allAccess` basis, and the real birth → install → share → start → enrol
→ authenticated GET `/` route. A PASS means HTTP 2xx or 3xx after that lifecycle; redirects
are recorded without following them. This does not certify an app's writes, external
services, co-editing, or the public TLS edge. Featured write recipes remain a separate check.

Run as the hbox world operator from a source tree covered by its installer sudo rule:

```sh
export MINI_OPERATOR_UID=1001 MINI_OPERATOR_NAME=mini-operator
scripts/spk-platform/store-sweep.sh \
  --candidate /build/candidates/FULL_SHA \
  --out /tank/lanes/cx-store-sweep/results \
  --staging /tank/lanes/cx-store-sweep/staging --dry-run
# Remove --dry-run for the whole store; add --max-worlds 3 for a first batch.
```

Use a detached job with its own PID file and `box-wait`, as COORDINATION §3 describes.
The default index is fetched through `mini-market-fetch` and checked by the candidate's
`mini apps index-check`. `--index FILE` selects a recorded index. Dry runs need curl,
jq and Python 3, but do not execute the candidate's Linux binaries or start worlds.
Actual runs also need the ordinary world prerequisites, flock, xz and GNU timeout.

The package download is bounded by the candidate's `spk-host import-limits market-large-v1`
raw ceiling and verified against its package ID's SHA-256 prefix. The XZ index after the
SPK's eight-byte magic supplies the decoded-size hint. Either raw or decoded size above
`standard-v1` selects `market-large-v1`; a batch containing such a package gets that
profile. When the bytes fit standard, a bounded `spk-host qualify --import-profile standard-v1`
preflight also detects the native Cap'n Proto segment-count refusal and selects the large
profile for it. This probe runs in the fresh world's protected intake directory: native scratch
custody requires root/operator-owned ancestors, which a shared lane staging path need not have.
Before any app is installed, `world-import-profile.sh` keeps the grain profile and broker budget
consistent and restarts the exact broker if the segment limit requires the larger profile.
It refuses to change a world that already contains apps. Segment count is not inferred from
byte length or parsed in this wrapper.
Other preflight refusals are retained as evidence; the real grain install still decides the
app's verdict. The real Mini ingest verifies signatures and enforces the actual decoder bounds.
Decoded sizes beyond the large profile are reported as `FAIL package-size`; downloads beyond
its raw ceiling fail at `fetch`. Neither is silently omitted.

Every complete world, including teardown, holds `flock -o $WORLD_UP_LOCK` (default `/home/hbox/lanes/world-up.lock`).
No lock descriptor reaches resident children. Every app is stopped after its probe;
`world-down.sh` and then `stop-residents.sh` run before deleting this invocation's staging.
Partial world-up records enough identity for world-down. Cleanup failure retains staging
and stops the sweep. A later invocation recovers its recorded interrupted staging under
the same lock before starting another world; unidentified or another run's staging refuses
recovery. SIGKILL before the staging identity is written therefore requires inspection.

`OUT/FULL_SHA/records/*.json` is the resumable source of truth. A completed PASS **or FAIL**
is skipped for the same candidate and exact package; a different candidate or package is
unjudged. Interrupted apps with no verdict are retried in a fresh world. Each atomic record
regenerates `verdicts.tsv` and `qualification.json`; startup regenerates both too, so a crash
between their renames loses no verdict. Results name the failed stage and native refusal
when available. World setup failures are reported as `FAIL world-up`, not app incompatibility.
After fixing a cause, `--retry-stage world-up` (or another failed stage) explicitly moves
those FAIL records into `records/history/` before replanning; PASS rows are never discarded.
When `--index FILE` selects a subset, only failures in that index are archived and retried.
With `--dry-run` this previews the retries without changing the recorded verdicts.
Evidence includes journey outputs, HTTP bodies/headers, logs and driver/binary pins. It is
private operator evidence and may contain credentials; publish only the summary.

The clean catalogue distribution point is `deploy/market/store-qualification.json`, embedded
in `mini` at build time. This makes the recorded summary travel with each candidate without
adding member-side network access. Copy a reviewed sweep's `qualification.json` there to
ship its evidence in the next candidate. An operator can read a newer recorded file with
`mini apps search --qualification FILE` (or `MINI_APPS_QUALIFICATION=FILE`), also for `show`.
Both text and JSON expose the result, keyed by **appId plus packageId**, with candidate,
scope, import profile, stage and evidence. Missing entries say `not swept`; malformed
summaries refuse by name. Qualification never changes the local ingest verdict or authorizes
an installation. A known-working badge always identifies the candidate actually tested.

Checks:

```sh
python3 scripts/spk-platform/test-store-sweep.py
CARGO_TARGET_DIR=/Users/ember/dev/minidregg-lanes/target-integ \
  cargo nextest run -p minidregg-resource-client -E 'test(apps_store_sweep)'
```
