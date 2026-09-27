# Read-only committed dispatch inspection source gate

`Host/ApplicationDispatchInspection.lean` decodes the strict
`DREGG/APPLICATION/DISPATCH-COMMITTED-PERMIT/v1` frame and renders its full
request, ordered headers, identity, effective bits, roots and original receipt
as decimal-string/lowercase-hex JSON. `Host.Main` exposes it as private
`inspect application-dispatch-committed INPUT.bin OUTPUT.json`. Input is
bounded by `FnEvidenceCodec.maxHostFrameBytes` (12,102,760 bytes); compact JSON
is bounded by eight times that (96,822,080 bytes) and otherwise refused.
`frameHex` repeats the exact input bytes so a physical host can compare the
inspection to the private op34 response it retained. Parsing or presenting a
frame does **not** prove CAS provenance and never constructs a `Permit`; only
the fresh op34 callback can hand off a committed frame.

One serial Lean process at a time compiled the helper and then Main in the
separate writable overlay
`/home/ember/build/minidregg-dispatch-inspect-overlay`. The overlay wrote
only its own OLeans/IR/logs. It imported read-only, source-qualified OLeans
from `/home/ember/build/minidregg-dispatch-final-20260927-spkcompat`; the
`Host.Json` OLean was copied as a plain file from the certified 9aec build
to match the committed custody source. No hardlinked build artifact or frozen
source was mutated. Both bounded invocations used one Lean process,
`LEAN_NUM_THREADS=2`, `MemoryMax=64G`, `CPUQuota=200%`, and exited 0:

```sh
LEAN_PATH="$overlay/olean:$base" lean Host/ApplicationDispatchInspection.lean \
  -o "$overlay/olean/Host/ApplicationDispatchInspection.olean" \
  -i "$overlay/olean/Host/ApplicationDispatchInspection.ilean" \
  -c "$overlay/ir/Host/ApplicationDispatchInspection.c"
LEAN_PATH="$overlay/olean:$base" lean Host/Main.lean \
  -o "$overlay/olean/Host/Main.olean" \
  -i "$overlay/olean/Host/Main.ilean" \
  -c "$overlay/ir/Host/Main.c"
```

Here `base` is `lake env printenv LEAN_PATH` from the read-only dispatch-final
snapshot, and the commands ran from the overlay root under `systemd-run --user
--scope --collect`. Captured logs `dispatch-inspect-helper.log` SHA-256
`430626fcd2f8697f07a4bd9fa9acf58ecb6b390c24a9304c3a12b03544d286e6`
and `dispatch-inspect-main-current-json.log` SHA-256
`32615e82ed410dd31ca499c7306906ff61fad7422511125280bba82697eff2fe`
contain no Lean diagnostics.

| Module | Source SHA-256 | Compiled OLean SHA-256 |
| --- | --- | --- |
| `Kernel/NativeHostReplay.lean` | `bcbf2b45c0bfbc29d6c0a98f9b1bb853c269f5981b81a7ad154297f534588230` | `10bdd5692b6754e18bb85cc974811b1a5b22f4c72ed3e1abd66c870e23ba09f2` |
| `Kernel/ApplicationDispatchReceiver.lean` | `d1c3a0a1e65ed8185dc1ec0fb3384392ef83b889c34f13d57cca9015b2a329fe` | `8e46f716436a9d32f4257df63e37c8a1c3eaa00809b7e050632db4c2bbc3d3c7` |
| `Kernel/ApplicationDispatchLookup.lean` | `5b2e1f77c78913cd6f2fe591a5d3b5c52cffd577ea5b57ec6de7e0b2cf030ae2` | `d3f86e0756be1b4fa84d5e435f38f8b47f5585d513a599cfe5594b69e5ff413d` |
| `Host/Json.lean` | `4b47dd92f0dbe90491ceca48b9aeacda722f42358d2f2aa76d6ef62002a2fa7f` | `e94fffe0e3ee921cc00fccdbc3cf8e13702c62665cb0cc4535ff0f601295e919` |
| `Host/ApplicationDispatchInspection.lean` | `43849e22779c0e6e56e7a1faf789089905a2775b969786d01d4756ca2137c4d8` | `c22f2fa439a5a018f43ed9806b28ea8bd8236bc45d3e59f6da2c8ebc10238629` |
| `Host/Main.lean` | `262775b1f5843597e55b0a4c8149a2f630a7a328af14fffc5a42b006646b39fb` | `9fef3a36b256d15c780054b5efd09bb93d861cb7d6331817c593fdec2b24b0ea` |

This is a source/OLean gate only. There is no newly linked native Host,
physical op34 response, or hostd HTTP delivery acceptance in this cut.
