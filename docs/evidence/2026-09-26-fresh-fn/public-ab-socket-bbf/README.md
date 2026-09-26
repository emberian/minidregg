# Fresh two-socket fn ↔ Mini exchange on qualified bbf52159

The isolated 2026-09-26 run completed with 79 accepted steps and outer exit 0:
`EXCHANGE COMPLETE`. Newly generated B and A Mini deployments had different
genesis bytes, gateway custody keys, and gateway subjects 7 and 17. Each
content resource 600 had the exact current `request/subject` gateway law;
ordinary subjects 8 and 18 remained separate. The fn Stores ran under fresh
hbox scratch `/tank/fn/scratch/mini-ab-bbf-20260926-2`; this was not a live
owner deployment.

Fn used the completed qualified image
`/tank/fn/gates/qual-bbf52159-20260925/build/images/bbf52159dcab19228bd6cd0b855b99dd6d68758d`.
Its 58-file `image.sha256` manifest SHA-256 is
`2d12deb4adcdfe439e3d38ecacc593c59e191b7e2f5c0f2819d883d4c5ef83c4`;
the `fn-host` launcher and core hashes are retained in `fn-image-pair.sha256`.
The source-matched Darwin Mini host was the committed-9004 A+skip checkpoint,
SHA-256 `82a7a6a596b8083a08c65aee8aeb0752d54b750b249899b59612130c5d7f97bd`.
Its source manifest SHA-256 is
`9a275a95dd2b8214d3885f2bf96188293c3529833dd58d24c5794f83119a1c87`.
The Rust client SHA-256 was
`0523c8d2a340da315c926b1c73d25f0bb6d5be647d3492841bfc2c589fff6014`.
The copied fn runbook started from pinned source SHA-256
`c88160cf459d3959928f6ae913f455ed9ff49971b89619518ab7b49c884c99e6`;
its per-side, Q creation, B socket and A socket patch chain yielded adapted
SHA-256 `56b62030f1f5918a3adece9aa51e9e2d1351a0ecf3962c337d04f7657dd1d367`.
The Mini fn bridge used for this run had SHA-256
`aa318febcfc17ecc3f8868ee3e03c9abb07c8c15d2587a4657d571b71b42f39a`.

B's separate persistent Mini socket returned a typed op12
`accepted-decision`/`proposed-fresh` with `observed-control-poll` (step 38).
The 206927-byte reply frame SHA-256 was
`d4231620a7900fb2e65c3bfe10b2ea93e46cfefc6a5f46344348539effda37fa`;
its 102772-byte intent SHA-256 was
`9bc05073e111b3b991d3520ff7d2ef83361e61139925fc2dd5fae514242559e8`.
Gateway custody signed and installed Mini accepted count 2 (step 39);
accepted export matched the preview cursor (steps 40–41). Typed op13 ACKed
by the Mini transaction ID alone, returning `durable-accepted` and fn Store
sequence/transaction 3/3 (step 42). Native fn position matched the retained
export (step 43).

A used its **own** persistent socket and operator-pinned R carrier, R/Q pins,
Q claim, scope, policy and fn control. Typed op14 returned
`accepted-decision`/`proposed-fresh` (step 71). Its 47487-byte reply frame
SHA-256 was
`d2a2453479e8a52b23ef06ac7be278b3a5d604dcf7413001ff10f47127842a8c`;
the 23361-byte intent SHA-256 was
`5cb55ef0e3fdb8da92f0007c659318e54079bf5b4d8d18b1e5bd123714e22aec`.
A gateway custody signed and installed accepted count 2 (step 72), the exact
result export passed (step 73), and typed op15 ACKed by A's accepted Mini
transaction ID with `durable-accepted`, fn Store sequence/transaction 6/6
(step 74). Native position matched export (step 75); final fn group counts
were two articles in each Store (step 78). The native run summary is private
`/tmp/mini-fn-final-ab-bbf-20260926-retry/run/summary.json`, SHA-256
`2dad900078753b494fa34b10229d6f61eace647d8c5cce6cd64f575adf9e15f0`.

The first fresh bbf attempt stopped before B poll because the Mini bridge
whitelist lacked the new read-only `consumer status` verb required by Host
op12; its 94-byte refusal frame said
`fn local consumer status refused or was uncertain`. Adding exact `status`
and `consumer-inspect` bridge routes allowed this new, independent retry to
pass. After the successful run exited, the bridge's hardcoded post-ACK empty
poll assertion was removed because a legitimate ACK can leave further Store
events; that later bridge version SHA-256 is
`4261c44a801059249454c6e4a6f3f3203f5b6dcb4d678bd0c0f479d45c5b8f05`.
The historical run used the earlier bridge hash above. This trial used the
small R/Q fixture; it does not demonstrate a larger-than-legacy evidence
article or empty-page progress.
