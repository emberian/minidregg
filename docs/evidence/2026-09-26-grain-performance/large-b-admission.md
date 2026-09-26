# Private large B admission timing

The exact 734,222-byte signed B call from the completed run-5 exchange was
submitted once to each of three independent private accepted-1 Store copies on
Persvati. No live or retained Store was opened for mutation. The accepted-1
preimage was reconstructed from the original pinned genesis and exact signed
birth call; its birth outcome matched run-5 byte for byte. The preimage SQLite
SHA-256 was `8eff8dd1c0a424ff75456da1adcc22c06774eab29238af001916b0a398404893`;
the signed call SHA-256 was
`59b6a3ac9a12a8552547833e1922ac7d3d9086ab1c26b404e10af3a9d60b952f`.
The configurations differed only in private `storageRoot`.

| Linux host | SHA-256 | Elapsed | User CPU | System CPU | Peak RSS | Approximate pre-write / post-write |
| --- | --- | ---: | ---: | ---: | ---: | --- |
| Selected bbf | `775a98c704e98b8a3065b2a93e9659aacf8f731f31d38b6360607e6bce64af19` | 456.94 s | 445.68 s | 11.05 s | 1,721,276 KiB | 202 s / 254 s |
| Linear cSHAKE, before loaded-byte observation | `41647562c7dd1fe6cdf41836aa62c61fd7b24314f883b2bb14cb38779707c49a` | 201.13 s | 193.72 s | 7.23 s | 1,723,952 KiB | 91 s / 110 s |
| Combined native image with proved hashed cast decision | `4bb72e1e984de413ee0065d7d229dbe0217bf980b4563ba26dc85ee38ed59c65` | 189.68 s | 183.43 s | 6.14 s | 1,391,948 KiB | 84 s / 106 s |

All three submissions exited successfully. All produced the **same 132-byte
outcome**, SHA-256 `caf4009a43d3cd6f6773f971574a0b4c5597e716f4d04640b1f6b3c54d7c42ee`,
which also matches run-5, and byte-identical accepted-2 SQLite images, SHA-256
`0066f07fcfd6d92fd95717c809fbab173b74d45be604841bb8fc3899884d82a5`.
Thus the first pair confirms a roughly 2.27-fold elapsed improvement on the same
large signed call and durable result. The linear binary also includes later host
endpoints, though the inspected native submit, receiver, durable IO, and
observation modules were byte-identical between these two frozen sources; the
linear cSHAKE change is the relevant changed submit dependency.

The third run used a fresh copy of the same accepted-1 SQLite image (preimage
SHA-256 `8eff8dd1c0a424ff75456da1adcc22c06774eab29238af001916b0a398404893`)
and the same call SHA-256. Its config differed from the linear run only in
`storageRoot`. The certified Linux image passed 169/169 source and 4/4
artifact checks. Relative to the linear image, the native submit, replay,
durable IO and cSHAKE source modules were byte-identical; PredCompile changed
to the proved hashed decision. The new image also includes loaded-byte
observation work and later Host endpoints, so this pair is a native-source
comparison rather than a strict single-module ablation.
Observed elapsed fell 201.13 → 189.68 seconds, user CPU 193.72 → 183.43
seconds, and peak RSS 1,723,952 → 1,391,948 KiB. This is one run per image,
under different ambient activity, so the 11.45-second wall difference is a
scoped observation rather than a general latency claim. Persvati had 24
online CPUs and no observed CPU quota throttling; load averages at the third
run's start/end were 4.56/8.35 (one-minute). The host used approximately one
CPU throughout. The byte-identical outcome and Store show no admitted
behavior change in this fixture.

The phase split uses the private SQLite file's modification time as the durable
write marker and the outcome file's modification time as the end marker. It is
an estimate, not an instrumented function-level profile. The linear and
hashed runs also recorded explicit start/end timestamps. The old run's start is inferred from
`/usr/bin/time` elapsed and its end-file timestamp. The large post-write cost
is consistent with `NativeHost.confirmed` reopening and semantically replaying
the Store for exact historical receipt readback. In a persistent stdio session,
`Host.Main.sessionConfirmed` instead refreshes a verifier-minted tip and
`NativeHostReplay.extendVerified` checks the old prefix exactly, then admits
the newly appended suffix. At accepted 1 → 2, that suffix is this large call;
the one-shot post-write timing must not be presented as measured session cost.

The private submissions were run with `/usr/bin/time -f
'elapsed=%e user=%U system=%S maxrss=%M'` around each host's `submit`
command, using the same call bytes and separate copied Store paths. No timeout
was changed. The combined linear-cSHAKE plus loaded-byte observation binary
`eddffd827496eb2a005af45158089957bacf63b019c8c3441b01b76b71db33b1`
has **not** been measured on this large call, so this evidence makes no latency
claim for the loaded-byte optimization in isolation; the third binary also
includes that change.

For a read-only follow-up, GDB launched the linear host as its own inferior
against a separate private copy of the accepted-2 SQLite image and ran
`describe`. Four bounded interrupts sampled the active Lean worker. One stack
was in `DurableReceiverIO.loadBytes → DurableReceiver.replay →
IntentRecord.bind? → ResourceBirthCodec.rootBytes → cshake256Bytes`.
Another was in `NativeHostReplay.walk → derive →
DeclaredResourceController.admit → projectCommonSlots → requestFor →
cshake256Bytes`. The remaining two were inside `List.dedup`/`pwFilter`
while deciding `castInjOn` for `intsOf` through
`DeclaredResourceController.authorizeLeg`. The inferior completed normally.
The copied SQLite image retained SHA-256
`0066f07fcfd6d92fd95717c809fbab173b74d45be604841bb8fc3899884d82a5`
after the debugger exited.
These are stack samples, not a percentage breakdown or a benchmark under the
debugger. Source inspection locates the latter path at
`Compiler/PredCompile.lean`'s `castEntries`, which deduplicates all old and
new state integers before the exact field-alias check. A separate compiler
edit now proves a membership-preserving hashed decision and retains the
original kernel-reducible decision through a proved `@[csimp]` equality.
The sampling preceded the third, source-matched native run; the alias check
itself remains mandatory.

The compiled decision repair in `Compiler/PredCompile.lean` has source SHA-256
`46d082cbbe605df7472a5181f90d180f172a6ef960ec1af78921a39fc5b0c052`.
Its full module and direct `PredCompileOrderWitness` module compiled in a
separate warm snapshot. The generated C for
`instDecidableCastInjOnOfDecidableEq` calls `castInjOnDecidableFast`, while
kernel evaluation retains `castInjOnDecidableSpec` and its original reducible
`castEntries`. The general membership/alias-equivalence theorem and the
`@[csimp]` function equality report only `[propext, Classical.choice,
Quot.sound]` in axiom accounting, with no `sorryAx`. The focused
`Compiler/PredCastHashProofs.lean` module (SHA-256
`6cb647b52735c6c60b615ce5bce0090099f5367b10554536627846d301cf38b2`)
also compiled. These are proof and code-generation checks, not an admitted
large-call latency measurement; that separate native measurement is in the
table above.
