# Agent dispatch event21 source checkpoint

This is a **narrow direct-Lean source gate**, not a native Host link, physical
SPK request, or two-participant acceptance. It uses the certified 589b62c
source/OLean base at
`/home/ember/build/minidregg-overnight-20260927-completion-next` and the
separate writable overlay `/home/ember/build/minidregg-event21-lower-check`.
The certified base Replay OLean remains SHA-256 `f713c0dcd4ac30c2f642362e28f4ec99a7bc33a6ca65607a8fe0c554f18546f8`;
the base `NativeHostContext` source/OLean pair is
`e88927f66ab0b1e806e9842e6d67c0f74b551a433acd83318eeeb0bd81c036d4` /
`57f2364ea0a1d960328aa4a4e6c8f961d0072b662c45e54f359e615a3b637616`.

| Exact source (`Kernel/*.lean`) | Source SHA-256 | Overlay OLean SHA-256 |
| --- | --- | --- |
| ApplicationDispatchCodec | `a1125bb80981883dbbf5d69367f00e8937545594f8ac94b8de375c20d664d749` | `23d1e74b13cb1286bc543f47709f5db393571dd311250810fe2a0a553a0c160a` |
| ApplicationDispatchAgentReserveContext | `b886b27f164afa41d769ee18823058ef2fa76222a947b98cfec83c9c69c93061` | `d011a03e8cf86f8a1cd16866543d7389b81c464673ebf97471f86e1439c949f5` |
| ApplicationDispatchAgentPayer | `47e217555b4d4165c635c3b2a8951b7730acb3b7158c46129d45c27ec7359b00` | `53aa74cb53ced3bf3df5705bea0d5ef47e393f1a1a72894e0b7d36f811938399` |
| ApplicationDispatchAgentReserveCore | `7961bffa211d5a25a9798adb8997eda64ffa8bf45a6229b975d9f21824989995` | `d43c969c9250084a73b07f9fa67ecbd937ba669f8013850d40ab5816af93b20d` |
| ApplicationDispatchAgentIngress | `f12062899371abee8a76e03cc78535060eb4e6550d757454d85035c915a8d951` | `9785980a7dc70bbdf9efcfda7d2439227f11c2639e5379ff5f91c0aa91935aa6` |
| ApplicationDispatchAgentCore | `b8f6ba3cba0870c4b2467087f9564b8bf3da9c32c9cec56f9373bd14fd9c5344` | `a6e9d7a9acecc8d4a03500d8cab6b9d8ebf4e6cf31d2f8e01d0aadad21138c08` |
| NativeHostReplay | `0d1338a0f588cbd78428b6d9b8b32eeb2b7027286aae37b3b995e833638a24ad` | `7a6b48a5fa84d1b011c97089a232537525be63409ce7ccdbd7a8d8258fe0e0bc` |
| ApplicationDispatchProjection | `99d334fb291afa5bdcd79727ff75d4a57f023eff56b6ac92f2c672db4a70fb15` | `ca5ef47debe9a178cb923d53ecf9e71dc6a666fd27d7c0f98230155e0da585f9` |
| ApplicationDispatchAgentProjection | `719d1d485921ccd54bc2498a51d83a770bd1fe4d23753f1b8de35d45e3a1fd7b` | `6aaeb611005d9bb78e3272657f9de85c543dc012ffd929bf9bf36e2d1d7693de` |
| ApplicationDispatchAgentReceiver | `be5489034baecb6a11b5eeb9dc35545d893d97897f21e4b90d76dd64ae01decc` | `a955e7c50a6af3edf1327008127210ae514588681f9e6175eb95414aa94d33f1` |
| ApplicationDispatchAgentLookup | `d4079bf347059f61284113c7f0c4ec620b541af18cc241d4e150d797b62a6661` | `8221396958e65d824da81881379a522f8a067c6328dcf21f9df270e0db2684d3` |
| ApplicationDispatchAgentAuthoring | `f9d1c9a3a855479bf82921230a522f450bb44c995fce53f673ed7fc40a99c68d` | `c73e2b62228b45428e258ec8243961e1447ce722e44486cb68166218a914b5fc` |
| ApplicationDispatchAgentPaidAuthoring | `4c0b86c4e9d7e447d65542d6d6b6d2840beccbde5a3438f5bfdf9145e615f510` | `9c9c41588618224535e73b073a222f46484971b803e07d4c021d73ac9c1fb549` |

The serial command for each module was, from the overlay directory:

```
base_path=$(cd /home/ember/build/minidregg-overnight-20260927-completion-next && /home/ember/.elan/bin/lake env printenv LEAN_PATH)
LEAN_PATH="$PWD/lib:$base_path" LEAN_NUM_THREADS=2 /home/ember/.elan/bin/lean Kernel/<Module>.lean -o lib/Kernel/<Module>.olean
```

Compilation order was Codec, ReserveContext, Payer, ReserveCore, Ingress,
Core, Replay, Projection, AgentProjection, AgentReceiver, AgentLookup,
AgentAuthoring, PaidAuthoring. Replay log
`/tmp/NativeHostReplay-event21-join.log` on Persvati has SHA-256
`3466e88f21218fe7c070c50a9908a0d67b1b5c726a8280006163c771fdbcd1e3`
and no Lean errors. Final dependent logs `/tmp/<Module>-event21-final.log` are
empty (SHA-256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`).
No whole native link or physical integration was run for this cut.

Replay retains a compact original reserve certificate only for an exact
single-target AgentGrain reserve shape, and only after native ordinary
admission, full retained-record match, durable advance and post-image
validation. Event21 requires an earlier admitted share issue, the exact
original reserve record/receipt and nonce/target binding to the full v2
context; it rejects any intervening purse-cell write. Fresh current app,
parent and payer checks form an event21 intent with a physical purse read
guard and one-use reserve-receipt claim nullifier. The receiver mints a
private committed permit only on exact CAS readback/validation, then offers
distinct framed `DREGG/APPLICATION/AGENT-DISPATCH-COMMITTED-PERMIT/v2` bytes
after a fresh point-in-time tip read. Lookup checks the event, transaction,
base and reserve-claim nullifiers and original receipt, but returns only a
receipt. Candidate inspection is not authority.

The source reserve plan binds the full app/session/ticket/parent/purse scope,
fixed payer, amount, charge, operation and source-derived canonical HTTP
digest into an ordinary AgentGrain nonce. The deployed grain-runtime still
signs an older digest-only v1 payload, so its current reserve **cannot** pass
event21. Private Host op58/59 reserve plan/assembly, op48/49 paid app+payer
plan/assembly, source inspection, runtime custody migration and native/physical
two-participant tests remain required. The new grain-backed share issue event22
also needs a distinct historical adapter before its tickets can authorize
dispatch; this cut retains only previously admitted event15 issue evidence.
