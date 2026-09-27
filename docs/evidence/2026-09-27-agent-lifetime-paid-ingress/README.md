# Exact event26 paid ingress, structural inspection

`Host/ApplicationAgentLifetimePaidIngressInspection.lean` accepts the exact
retained op78 paid Plan bytes and the assembled event26 ingress bytes. It
decodes both through their source-owned canonical codecs, matches each app,
grant and payer signed envelope to its exact Plan slot header, recovers only
the detached 64-byte signatures, and calls the existing Lean `assemblePaid`.
It returns JSON only when the reassembled ingress equals the supplied ingress
byte for byte. The projection includes canonical Plan/ingress/context/HTTP,
grant and reserve selectors, original app/session origin, payer signed bytes
and source signing slots. Its type is
`application-agent-lifetime-paid-ingress-inspection-v3`; it labels its
authority `structural-only-not-fresh-admission`.

The inspector does **not** verify signatures, check the current image,
admit event26, or mint a fresh physical dispatch permit. It is designed for
a pinned two-input Host CLI: `inspect-agent-lifetime-paid-ingress PLAN.bin
INGRESS.bin RESULT.json`. Root added that route in `Host/Main.lean`, with
bounded reads and bounded JSON output. The helper and Main both compiled in
the independent 2649-based successor snapshot; no native CLI run is claimed.

Direct Lean typecheck passed in an independent Persvati overlay rooted at
`/tmp/mini-lifetime-paid-ingress-inspect-20260927`, using the certified
2649f49 source/OLean closure at
`/home/ember/build/minidregg-2649f49-next-20260927`. The command used one
atomically claimed compiler seat and `LEAN_NUM_THREADS=2`:

```
LEAN_PATH=<private-olean>:<certified-lake-env-LEAN_PATH> lean -o <private-olean>/ApplicationAgentLifetimePaidIngressInspection.olean Host/ApplicationAgentLifetimePaidIngressInspection.lean
```

The check exited 0 and produced an empty terminal log, retained as
`lean.log`. The emitted OLean SHA-256 was
`b5fce21910297ada0636464908d058b66f49413c3f25751f3eab367908fbd367`.
This is a source gate; no native Host route or event26 Store action ran.

The combined check used helper SHA `244f85f4ae9e4e2c37eff37a658e8edc7b4886b7396cf6d2a6e6abec981ce22d`
and Main SHA `505a81d45a0931aa8e87a3dcf8f4d911a4a3a199c22a8b643f50c9e2dcd1b6dc`.
Both emitted no diagnostics and exited zero in
`/home/ember/build/minidregg-capability-next-20260927`; the exact committed
successor still needs its native build and actual event26 acceptance.
