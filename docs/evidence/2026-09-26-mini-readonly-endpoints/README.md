# Mini read-only receiving endpoints: narrow source gate

`Host/Main.lean` SHA-256 `bc9cd9f45cbf9eb0d02d52ef2c93ab0cf8e38001b6c26a4b0a0e968b78d587b8` and `Kernel/NativeReserveContinuity.lean` SHA-256 `3a0c8923693d275f140ae74d69632c9b7f3b56877564a48f74f9d6dfe7f6cfc1` compiled sequentially with `LEAN_NUM_THREADS=2` in the exclusive receiver snapshot. Both produced OLean, ILean and C output with exit 0. The snapshot used the older fn event profile OLean; a coherent qualified-bbf build and linked runtime probes remain necessary.

Op17 accepts the original canonical signed call and confirmed Outcome bytes, refreshes the verifier-minted Mini session, and checks suffix continuity for an operator-pinned provider resource. It confirms only that the original reserve wrote the provider cell and that later accepted records meet the checker's conservative no-provider-rewrite/ordinary-ingress condition. It does not prove current parent authority or grant an atomic lease over a later upstream send; the runtime must retain its fresh signed parent/provider checks.

Op18 reopens an accepted signed tag-10 prepared-R outbox by canonical transaction ID and returns its exact retained carrier and both original receipts. Its historical selector does not require the current mutation grant. This is prepared local publication custody, not evidence that fn posted the article.
