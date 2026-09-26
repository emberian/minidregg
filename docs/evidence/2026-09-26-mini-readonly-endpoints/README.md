# Mini read-only receiving endpoints: narrow source gate

`Host/Main.lean` SHA-256 `bc9cd9f45cbf9eb0d02d52ef2c93ab0cf8e38001b6c26a4b0a0e968b78d587b8` and `Kernel/NativeReserveContinuity.lean` SHA-256 `3a0c8923693d275f140ae74d69632c9b7f3b56877564a48f74f9d6dfe7f6cfc1` compiled sequentially with `LEAN_NUM_THREADS=2` in the exclusive receiver snapshot. Both produced OLean, ILean and C output with exit 0. The snapshot used the older fn event profile OLean; a coherent qualified-bbf build and linked runtime probes remain necessary.

The commands ran in `/tmp/minidregg-overnight-20260926-receiver`, first with `MODULE=Kernel/NativeReserveContinuity`, then `MODULE=Host/Main`:

```sh
LEAN_NUM_THREADS=2 lake env lean "$MODULE.lean" \
  -o ".lake/build/lib/lean/$MODULE.olean" \
  -i ".lake/build/lib/lean/$MODULE.ilean" \
  -c ".lake/build/ir/$MODULE.c" --json
```

The captured `kernel-narrow.json` and `host-narrow.json` contain the compiler's package warnings; the commands exited 0. The dependency identities include NativeHostSession `2efb18a6…`, NativeHostReplay `af529000…`, NativeHost `0a8719b4…`, FnOriginOutbox `5fb063ab…`, Host.Json `0eed6d34…`, older FnInboxView `bc9ed421…`, and older FnEvidenceCodec `0d08d825…`. This scope must not be relabeled as the later complete native build.

The two commands, run in `/tmp/minidregg-overnight-20260926-receiver`, were:

```sh
LEAN_NUM_THREADS=2 lake env lean Kernel/NativeReserveContinuity.lean -o .lake/build/lib/lean/Kernel/NativeReserveContinuity.olean -i .lake/build/lib/lean/Kernel/NativeReserveContinuity.ilean -c .lake/build/ir/Kernel/NativeReserveContinuity.c --json
LEAN_NUM_THREADS=2 lake env lean Host/Main.lean -o .lake/build/lib/lean/Host/Main.olean -i .lake/build/lib/lean/Host/Main.ilean -c .lake/build/ir/Host/Main.c --json
```

Relevant snapshot dependencies: NativeHostSession `2efb18a6`, NativeHostReplay `af529000`, NativeHost `0a8719b4`, FnOriginOutbox `5fb063ab`, Host.Json `0eed6d34`, FnInboxView `bc9ed421`, and FnEvidenceCodec `0d08d825` (SHA-256 prefixes). The last two are older than the qualified-bbf source candidate.

Op17 accepts the original canonical signed call and confirmed Outcome bytes, refreshes the verifier-minted Mini session, and checks suffix continuity for an operator-pinned provider resource. It confirms only that the original reserve wrote the provider cell and that later accepted records meet the checker's conservative no-provider-rewrite/ordinary-ingress condition. It does not prove current parent authority or grant an atomic lease over a later upstream send; the runtime must retain its fresh signed parent/provider checks.

Op18 reopens an accepted signed tag-10 prepared-R outbox by canonical transaction ID and returns its exact retained carrier and both original receipts. Its historical selector does not require the current mutation grant. This is prepared local publication custody, not evidence that fn posted the article.
