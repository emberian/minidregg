# Live 64k Bonsai invocation deadline

This is a readback addendum to the [65,536-token local service
qualification](../2026-09-27-hermes-context-64k/README.md), not a model or
configuration change. On hbox, transient user unit
`bonsai2-ptq1-local-64k-v1.service` began at **2026-09-27 21:16:33 EDT**
(2026-09-28 01:16:33 UTC). Its `RuntimeMaxUSec=2h` gives an automatic stop
deadline of **2026-09-27 23:16:33 EDT** (2026-09-28 03:16:33 UTC). The
[before readback](before-status.txt) showed about 1h43m remaining.

There were no active TCP connections to port 18081
([socket readback](connections.txt)). An authorized attempt to extend the
**same** live invocation using systemd 256
`systemctl --user set-property --runtime bonsai2-ptq1-local-64k-v1.service
RuntimeMaxSec=6h` was [refused](set-property.log): systemd cannot set
`RuntimeMaxUSec` through that API. The before and after unit-property
readbacks are [byte-identical](before.txt), [after](after.txt). The post-call
[status](after-status.txt) still shows the original deadline, and the
[listener](listener.txt) remains loopback-only. PID `3457733` and invocation
`1a3be0a0dacb42cf92a826a454d7cbeb` are unchanged.

No restart, second GPU load, model request, auth change, or unit-file edit
occurred. The bounded unit remains active with its original two-hour total
limit. If later integration runs beyond that deadline, it must first observe
the old unit terminal and deliberately launch a new bounded invocation from
the pinned source and artifacts.
