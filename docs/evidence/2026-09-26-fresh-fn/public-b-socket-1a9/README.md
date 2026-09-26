# Fresh B public socket exchange on qualified fn 1a9dd747

The isolated 2026-09-26 run used newly generated, independent B and A Mini
genesis bytes, gateway subjects 7 and 17, separate custody keys, and a
subject-locked content resource 600 in each Store. B's gateway configuration
pinned the current policy address as a canonical decimal string. The fn
servers and Stores ran in fresh hbox scratch; no live owner was changed.

Fn used the completed `qual-1a9dd747-20260924` image at
`/tank/fn/gates/qual-1a9dd747-20260924/build`. Its frozen manifest names
`fn-host` SHA-256 `60e14e2afe8703574a9d74d89dc632a6c030a668fa261a74d92dd7589bb686d9`
and `fn-host.core` SHA-256
`12ece6cc95f3c4bed7a5d0a1abcfa0e5ea25257855e3f5caed22007c9a7b2bdd`.
This is the previously qualified small-R/Q reader profile with a 196608-byte
Mini composite bound, not a qualification of larger v2 evidence through fn.
The source-matched Darwin Mini B host was
`/tmp/minidregg-overnight-20260926/minidregg-host-final-b-fast` SHA-256
`c2a1fd3699338f28eaf1d076b53cbd1bf27b4438b857b0482666205b334a394c`;
its source manifest is
`/tmp/minidregg-overnight-20260926/final-b-repaired-source-manifest.txt`.
The combined Rust client SHA-256 was
`0523c8d2a340da315c926b1c73d25f0bb6d5be647d3492841bfc2c589fff6014`.
The pinned fn runbook source SHA-256 was
`c88160cf459d3959928f6ae913f455ed9ff49971b89619518ab7b49c884c99e6`;
a private copy applied the committed per-side, explicit Q creation context,
and B socket overlays. Adapted copy SHA-256:
`1aee81919f5be8f47ab6c3e16b5a185ab8113ee31e8eb903f36fe1bb77f0ae23`.

The B route used one persistent `mini serve` socket and its operator-pinned
`fnPoll` paths. Native step 38 returned a typed
`fn-consumer-poll-session-v1` accepted decision, with
`storeAdmission=observed-control-poll` and `decision.type=proposed-fresh`.
The framed response was 207123 bytes, SHA-256
`73adf08e57d501ca14a94cb45675eaabb6402f46074944a52821033da23c7043`;
its returned binary intent was 102870 bytes, SHA-256
`b7b3b149f6b1a7dec1bd240328d52ed044dc56881c1dd5c6d554cc38463cc506`.
Step 39 submitted that intent, signed by B gateway custody, through the same
socket and installed Mini accepted count 2. Steps 40–41 exported the accepted
operation and checked its exact fn cursor against B's preview. Typed op13 at
step 42 ACKed using only the accepted Mini transaction ID and returned
`fnAck=durable-accepted`, fn Store sequence/transaction `3/3`. Step 43 checked
the native fn position against the retained export. The ACK JSON SHA-256 is
`31087154654b45587b888a1429d3f9d000c00d96e050acd024841f1e9ba58f06`.

The rest of this B-only-host run did **not** complete the A ACK. A's direct
reply decision, signed Mini submit, and accepted export reached steps 70–72.
At step 73, the older B-only host's direct `reply-consumer-ack-poll` refused
with `fn E1 source has unsupported headers`: that host used the R source
parser on the Q MIME source. The specific log SHA-256 is
`29b76a049b7258fd5f6c1d48b4aa713390919751314351c1c4a4b0466d688ba7`.
The outer recipe exited 1 and reported `STOPPED`; B's typed transaction and
ACK remain separately accepted. The private `summary.json` has 74 steps,
SHA-256 `5f560f40ab519014f773438e33a3357bddf52cf718e6b02ebd32baa681dec4b8`,
under `/tmp/mini-fn-final-b-socket-20260926/run/`. A corrected A host and
fresh two-socket run are required for the full exchange.
