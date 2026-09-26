# Linear cSHAKE256 absorption gate (2026-09-26)

Source commit: `7941bcd`; `Compiler/Sp800185Cshake256Core.lean` SHA-256
`c4c8aa4b7cf7b61817803426d728a8a6e51321a3b0d96042117d190b8aae0ba0`.
The prior indexed absorber rescanned the list prefix for each 136-byte block.
The new executable carries the remaining suffix forward. The general Lean
theorem `absorbPadded_eq_indexed` proves identical state for **every** input
byte list, including non-rate-aligned lists. `cshake256Bytes_eq_indexed`
connects that equality to every customization/input pair and exact output.

In isolated warm snapshot `/tmp/minidregg-overnight-20260926-session`, with
`LEAN_NUM_THREADS=2` and one claimed Lean seat:

```text
lake build Compiler.Sp800185Cshake256Conformance                 PASS 809/809
lake env lean Compiler/Sp800185Cshake256Conformance.lean         PASS
lake env lean /tmp/minidregg-cshake-axioms.lean                 PASS
```

The conformance module checks the published NIST SP 800-185 cSHAKE sample 3
and FIPS 202 SHAKE256 empty-message vectors. The exact command outputs are
[`conformance.log`](conformance.log), [`vectors.log`](vectors.log), and
[`axioms.log`](axioms.log). The axiom readback is:

```text
absorbPadded_eq_indexed: [propext, Quot.sound]
cshake256Bytes_eq_indexed: [propext, Classical.choice, Quot.sound]
```

This proves byte preservation, not a physical runtime improvement; native
latency must be measured separately on a source-matched executable.
