# Accepted B empty-page progress after 17 neutral fn events

The isolated qualified-bbf B run completed with 111 harness steps. It first
registered 17 unrelated fn consumer events, then used two locally observed
empty-page polls. Mini accepted one signed tag-9 progress command for 0→16
and another for 16→21; the first exact retry after a Mini restart produced
no new intent. The harness then posted the matching R article and completed
the ordinary B operation. The fn ACK itself appends another Store event, so
the harness ended the initial wake after the short second page instead of
waiting for an idle poll.

After the owner and Mini service stopped, `scripts/probe-fn-accepted-skip.lean`
reopened the completed B Store through `NativeHost.openExisting` and scanned
accepted Mini events with `FnConsumerProgress.originalSkip`. It recognized
exactly two skips, 0→16 and 16→21, in a bounded cursor chain. That selector
requires the complete signed command to equal `progressCommand`, whose sole
action is one tag-9 progress atom; no application operation, reply, result,
or outbox atom is present in either recognized command. The bounded output
is [accepted-skip.log](accepted-skip.log).

Read-only inputs (not copied here): B config
`/tmp/mini-fn-skip-b-bbf-20260926-2/run-short/mini-b/config.json`, SHA-256
`44c62987ea87e9f06e738dceca35c69c2b255593760237d1bf9fbfbb43be0987`;
scope pin `/tmp/mini-fn-skip-b-bbf-20260926-2/run-short/b-scope-pin.json`, SHA-256
`754b309828770629809c826fbdbf68bc4ca5e2093fd9135098f3c7ce01ae6b4a`.
The probe ran against the coherent Mini selector snapshot used to build
`minidregg-host-next`, SHA-256
`b9ff9832b13ad67124e753ab52122732bfe9b795653e2ba64c1e0f35b051ee8a`.

Probe SHA-256 `e80f1631d6d9d800093de64fc230ce27e640544b8d24e8b7fb7b773649052b4c`;
log SHA-256 `d228719771c8d3343b3b4ab0aeae4a8ee3ca6069b16400a95496790966c785be`.
This check reopens accepted Mini history. It does not itself poll or ACK fn.
