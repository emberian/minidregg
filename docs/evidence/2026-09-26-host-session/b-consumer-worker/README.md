# B consumer worker: protected wake and bounded native drain

This isolated 2026-09-26 run used a real fn Store owner, NNTP STARTTLS listener,
Mini Host/Main service, and Rust client. The fn Store fixture lived under
`/tmp/mini-fn-drain-fixture-20260926` and was private; this record includes no
keys, passwords, raw calls, payloads, or store images.

The native host was `minidregg-host-a-claim3` SHA-256
`39fd1db2ab4e488b4aaf7d0a00cfba781c42c40bef5c2a1139d80769be7ad8ee`.
The first one-shot test used immutable drain-core client SHA-256
`6a0eb188589b50aa5f8699a8ed7a9dbea363540e4a07960e3e347134c672dbb7`.
It consumed fn neutral pages 0→16 and 16→21, obtained two distinct Mini
confirmed receipts (accepted counts 2 and 3), received `durable-accepted`
op13 ACKs for both, and stopped after the short page. Both exact transactions
were archived in the private worker state; no pending slot remained.

The unattended scheduler binary SHA-256
`0ed346fd4c41a1e5f7a91252e6d4d0a396eac96232b9fcd86681e8a969c39367`
was built from current client source files with SHAs: `main.rs`
`6fb1494f34260d9d772aafae4eb8ec262397a424fb2f6ec867be5524b83aad97`,
`drain.rs` `6c9684db4dc44e6dab3c76e0c28d010d0f603d2519269c2ee52f1fa78dc42d7a`,
and `worker.rs` `44b07cdd3a93d846f6ee29edf47265aacdd77614b8c3bb4ae3c3d1885ddc2bd8`.
The source is not yet part of a linked Host binary; Rust and Host are separate
processes, with the exact Host SHA above. Focused client nextest 16/16 and
clippy with warnings denied passed after the final source edits.

The fixture's fn certificate was a self-signed `CN=localhost` certificate
with `CA:TRUE` and no SAN. Rustls general WebPKI validation refused it;
the scheduler used an exact DER leaf pin, parsed and checked the localhost
name and validity, and delegated TLS handshake signatures to rustls. The
protected NNTP `GROUP fn.test` tuple began `(0,1,0)`. Starting from the
one-shot's completed state, the scheduler processed one ACK-only fn journal
event as a short 21→22 skip (Mini accepted count 4), then remembered `(0,1,0)`.
Across multiple 2-second intervals it made no further Mini write.

The operator then published and peered one genuine R from the pinned Mini
origin. Protected GROUP changed to `(1,1,1)`. Host op12 proposed the R using
verified source and origin evidence; the worker submitted its exact retained
call and obtained Mini accepted count 5, followed by a durable fn ACK. One
short ACK-metadata skip advanced 24→25 (Mini accepted count 6). The worker
remembered `(1,1,1)` and remained idle across multiple intervals with five
archived transactions and no pending slot. After a clean worker restart using
the retained hint, it still made no further Mini write.

This proves one genuine external publication wake and no recurring ACK-only
loop for these exact binaries and fixture. A second distinct R from the same
origin was unavailable in this fixture; it was not simulated by altering the
Message-ID of the same Mini origin package. Uncertain fn ACK recovery also
remains an operator hold until the newer coverage route is linked and tested.
