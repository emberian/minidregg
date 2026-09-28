# Upstream Hermes context gate and a real local 65,536-token Bonsai service

This is an isolated hbox measurement. The upstream Nous Hermes Agent source is
the retained clean `6d8a8bebf70b09554deda5a0fcd95facbbde7b07` checkout in
the [A runtime root](../2026-09-27-hermes-upstream-pair/README.md). Its
`agent/agent_init.py` SHA-256 is
`c83ae4badd9d80a3e05b6ea2bcb553072672f888a9712e9de279d6b6cc17511d`;
`agent/model_metadata.py` SHA-256 is
`8967a891a275c742331e986507bd34e7187eb84379748dd8fa30b1944fe65b4d`.
The unmodified source sets `MINIMUM_CONTEXT_LENGTH = 64_000` and
`_enforce_minimum_context` refuses a smaller custom-provider window. Its
specific LM Studio exception does not apply to this deployment.

The private no-network ACP probe used Mini's generated profile shape with
`model.context_length: 7168`, a synthetic token, and a rejecting loopback HTTP
sink. `initialize` succeeded, but `session/new` refused the 7,168-token window
before any model POST. [The keyless log](guard-7168.log) records the refusal;
the bounded [capture harness](capture-7168.py) was used only as a probe, not
as a worker implementation. Its SHA-256 is
`e31455ecbe47c8f7dbf8f79d945239b99fd5dca69a93ddbab6fdcb6e73fdcea0`.
All transient probe worker/controller units are inactive or gone, as recorded
in [cleanup](probe-unit-cleanup.txt).

For measurement **only**, a second fake-sink probe advertised 64,000 tokens.
This did not claim that the old 8k server supported 64k, and no model was
contacted. The real upstream ACP emitted a 35,808-byte first
`/v1/chat/completions` request with two messages and 16 built-in tools. The
[shape](request-shape.json) records its exact fields: streaming with
`stream_options.include_usage`, and **no explicit `max_tokens`**. The upstream
rough estimator counts the major built-in tool schema at 7,339 tokens alone;
the measured 8k profile was inadequate even apart from the startup guard.
The [fake-sink summary](fake-64000-summary.json) and
[harness](capture-64000.py) retain source scope and hashes. No Mini MCP server
was registered in these probes because the r3 Store has no accepted app
event22/27 lineage or complete GitWeb tool catalog yet.

The pinned GGUF (`53107f530aa52eb00912263ab1ee29bd199261c87cd7b4ad4ca1318c1fe33ee3`)
declares `qwen35.context_length = 262144`, 64 blocks, four KV heads and 256
dimensions per K/V head ([bounded header read](gguf-header.txt),
[parser](read-header.py)). Its existing 8,192-token unit had no active TCP
connections ([pre-stop observation](original-8k-connections.txt)); its exact
[unit configuration](original-8k-unit.txt) and
[status](original-8k-status.txt) were retained before stopping it. No original
model file, key file, service configuration, or artifacts were overwritten.

The new bounded user unit `bonsai2-ptq1-local-64k-v1.service` runs the **same**
PrismML server binary SHA-256
`f0321669b20397593e3ac09972bf6f4b7a0684954906565353b7ca84b4b0320f`
and GGUF, with `--ctx-size 65536 --parallel 1 --flash-attn on
--cache-type-k q4_0 --cache-type-v q4_0`. It has `MemoryMax=32G`,
`CPUQuota=200%`, and `RuntimeMaxSec=7200s`; its exact
[unit](64k-unit.txt) retains the full argv without the bearer value. The alias
is `bonsai2-27b-ptq1`, bound only at `127.0.0.1:18081`, using the existing
mode-0600 private key file. [The server journal excerpt](selected-journal.log)
confirms **one slot with `n_ctx_slot = 65536`**, model loaded and loopback
listener. [Status](64k-status.txt) observed an active unit, 6.92 GB systemd
memory peak against 32 GB cap; AMD VRAM use was 8,434,159,616 of
12,868,124,672 bytes. The old 8k unit was inactive and only the new listener
existed ([statuses](8k-after.txt), [listeners](listeners.txt)). Unauthenticated
`/v1/models` returned [401](unauth-code.txt).

Direct authenticated local inference returned HTTP 200 for harmless
[nonstreaming chat](nonstream-summary.json) in 3.98 s (65 prompt and 37
completion tokens), and for a [streaming tool call](tool-stream-summary.json)
in 8.16 s (six tool-call deltas, usage event and `[DONE]`). No external
provider or paid request was used. The key was read only into the private
test process and was not logged or copied into this evidence.

Finally, the exact fake-sink-captured upstream `Say hello.` request was sent
once to the **real** 65,536-token service with an explicit 512-token output
cap, mirroring Mini's strict gateway cap. It returned HTTP 200, `[DONE]` and
usage of **8,947 prompt + 23 completion tokens** in 140.74 s; see the
[keyless summary](upstream-baseline-summary.json) and
[server timing](selected-journal.log). This is the upstream built-in-only
baseline. The eventual Mini MCP tools add to it, so a complete GitWeb catalog
still needs an exact first-prompt measurement and admission check. For
controller config review, `maxInputTokens=65024` plus
`maxOutputTokens=512` fits the physically loaded 65,536-token slot and clears
upstream's 64,000-token minimum; this is a configured budget, not a claim that
every future tool catalog fits it.

The full captured prompt/request and model response remain private under
`/tank/dregg-preview/` on hbox. This evidence contains only request shape,
hashes, timings, counts and keyless logs. The new service is a bounded local
qualification, not yet a Mini provider/controller journey.
