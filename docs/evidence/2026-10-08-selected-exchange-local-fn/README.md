# Selected exchange through a local fn node, 2026-10-08

SHIP-PLAN R10: `row_exchange` passed twice through the real
`scripts/pipeline/journey-runner`, using Mini READY artifact set
`0ea31db53c5844c9e1676f1dc6b821ec9993da91`. One asserted wrong-owner-key
plant made the same row FAIL at recipient admission. All jobs ran sequentially
on this box; no external fn node or public host was contacted.

The journey initializes a fresh fn Store, certificate, posting principal and
consumer under the runner's private temporary scratch directory. NNTP binds to
`127.0.0.1:11241`; consumer polling uses that node's Unix control socket. Both
Mini services are stopped, and the fn child is terminated and reaped on success
or refusal. The runner also contains the row in its own systemd scope and
deletes the private scratch world. No custody key, signature or Store is copied
here.

## Inputs and sizing

Mini binaries come from
`/srv/artifacts/0ea31db53c5844c9e1676f1dc6b821ec9993da91/bin`.
The runner verifies the READY set's `SHA256SUMS` before each job. Exact hashes of
the Host, Mini, Store helper, verifier, journey and bootstrap are retained in
[green-1/input-sha256.txt](green-1/input-sha256.txt) and are identical in green-2.
[source-sha256.txt](source-sha256.txt) additionally pins the row, plant and
bootstrap dependencies. These are source-scoped runtime results, not a later
deployment qualification.

fn input is the frozen development image at
`/srv/fnbin/6679dae0e/fn-6679dae0e`:

| Input | SHA-256 |
| --- | --- |
| `fn-host` | `5a237d2ab830bfe6d0a23f9daecacb25054610834e4d6c617417fdf1d92dc227` |
| `fn-host.core` | `cd129ffbb3f92840f5738d708f5c49775b70abd661ca9d1216ce2bfc168fee2f` |

Every entry in its [image manifest](fn-image.sha256), including bundled runtime,
libraries and OpenSSL, passed `sha256sum -c image.sha256` before first use and
before each runner job. The input README describes lane source `6679dae0e`, no
release glibc floor and a 64 MiB collection trigger. This is development evidence.

The frozen launcher defaults to 32000 MiB dynamic space and accepts
`SBCL_USER_ARGS` after that default. The journey sets
`SBCL_USER_ARGS='--dynamic-space-size 8192'` for its local node and consumers.
This fits the runner's existing 24 GiB limit with headroom for Mini and fn
consumer processes; no row memory-limit increase was required. A preliminary
runner job `j479848041` failed before LISTENING with
`Peer flight startup refused: native worker reservation is not held.` The 8 GiB
setting resolved that failure in both independent runner runs.

## Jobs and pinned verdicts

| Job | Mode | Row verdict | Wall seconds | Retained pin |
| --- | --- | --- | --- | --- |
| `j479948502` | green-1 | PASS, exit 0 | 29 | [job.log:5](green-1/job.log) |
| `j479995435` | green-2 | PASS, exit 0 | 30 | [job.log:5](green-2/job.log) |
| `j480035360` | plant | FAIL, exit 1 | 30 | [job.log:7](plant/job.log) |

Both green pins are:

```text
GREEN exchange PASS: local fn stopped; exact selected packet admitted and signed readback verified
```

The plant harness exits 0 only after asserting the mutation actually applied,
the real row is FAIL/exit 1, and the retained positive-control outcome is
`refused`, phase `61646d697373696f6e` (admission), with encoded `request refused`.
Its [pins](plant/pinned-lines.txt) and
[exact outcome](plant/positive-control-outcome.json) attribute the red to the
wrong signing credential, rather than an unrelated startup failure:

```text
PLANT APPLIED: control release signed with Store B key for Store A owner
RED exchange FAIL: planted Store B owner key refused at recipient admission (positive-control)
```

The mutation is confined to a temporary journey copy: it substitutes Store B's
key for Store A's in the fresh positive-control release, while retaining every
journey assertion and all product code. With A's key that control is installed
in both green runs. With B's key the otherwise identical admission path refuses.

## What passed and limits

[public-summary.json](public-summary.json) is the unmodified second green
summary; each run's own summary and timings are retained separately.
[timings.tsv](timings.tsv) combines the timed steps with run/job labels, and
[jobs.tsv](jobs.tsv) distinguishes the plant harness exit from its row exit.

Each green run proves two independently credentialed Mini Stores exchange the
exact selected content through a locally started fn node: event14 before POST,
real stored-article extraction, recipient event13 admission, exact retry, and a
fresh signed recipient read. The stored body equals the packet and contains
the selected text once and the unselected text zero times. Altered article,
tampered packet, wrong signer and wrong root refuse at their recorded boundaries;
the recipient logical image is unchanged by those refusals. Row checks now
require the local stopped-node evidence, admission, disclosure and refusals.

This remains **transport only**: no schema-1 fn-e authorship verdict, event17
coverage or fn cursor ACK. The recipient's sponsor lockout is intentional; the
owner's enrolled home identity performs signed readback. There is no owner
recovery bypass, application installation or cross-machine claim.

## Reproduce one row

From the repository root, with these same locally available inputs:

```sh
bash scripts/kn2/plant-exchange-owner-key.sh --green \
  /srv/artifacts/0ea31db53c5844c9e1676f1dc6b821ec9993da91 \
  /srv/fnbin/6679dae0e/fn-6679dae0e/fn-host \
  /srv/fnbin/6679dae0e/fn-6679dae0e/fn-host.core \
  /tmp/exchange-green-new
```

Use `--plant` and a new results directory for the mutation. This wrapper supplies
`MINI_FN_LAUNCHER` and `MINI_FN_CORE`, verifies the frozen image, and invokes the
real runner with `--row exchange --source-tree` and the explicit READY tip.
It avoids `{bin}`, which initially resolved to a different cxo artifact set:
preliminary job `j479687155` refused `clockMaxStepSeconds` during bootstrap;
explicit base artifacts passed direct job `j479716445` before the runner work.
