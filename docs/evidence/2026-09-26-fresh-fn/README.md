# Fresh fn/Mini evidence, September 26

These are bounded public captures from two runs using Mini `183cd37`, host SHA-256 `0cce4fbd02c5b5156fb061e2d96f2e25e12588c35b59d2fd2efe20acb202f286`, and the qualified fn `1a9dd747` image pair. They do not exercise the new persistent host, new gateway pin enforcement, or repaired Message-ID parser. [The full scope and reproduction paths](../../FN-E1E2-TWO-STORE-2026-09-24.md) distinguish these runs from newer source checks.

- `distinct-steps.json` retains every harness step's verdict, duration and original log hash from the independent A gateway subject 17 / B gateway subject 7 run. Both sides use fresh distinct keys and genesis. The native exchange and owner cleanup completed. The outer shell wrapper subsequently exited 2 because its file was edited during execution; the recipe itself is not recorded as passing.
- `a-outcome.json` and `b-outcome.json` are the actual accepted Mini receipts from that exchange, each at its own Store's second event.
- `long-id-failure-steps.json` and `long-id-failure.log` retain the earlier fresh single-input run's A-side refusal. It generated a canonical digest encoding of 68 hexadecimal characters while the old parser expected 66. The independent-identity run happened to generate 66 on its first inputs; no key search was performed.

The step captures are projections of the original summaries, retaining only `cut`, `cut_reached`, `stopped`, `reached`, `reached_outcome` and each step's `n`, `step`, `outcome`, `detail`, `exit`, `seconds`, and `log_sha256`. Large intermediate facts, signed article bytes, private Stores and custody files are not copied here.

Original full-summary SHA-256 identities:

- Distinct: `5425858da0674fb0ace6c759a997bd9985af5b922a74877d09c5d264c5f318a6`.
- Longer-ID failure: `df1550ba26c2893142e893c336a17e126c92cf367636ad263df7913a94b7d062`.

The distinct run used a private copy of the fn harness, with only the recorded per-side Mini input patch applied: original source `c88160cf459d3959928f6ae913f455ed9ff49971b89619518ab7b49c884c99e6`, adapted source `fa595de896891cf362c8f8af3a8000d6ab8298d59837f0c8634b6807faaf2015`. The shared fn checkout and protected live node were untouched.
