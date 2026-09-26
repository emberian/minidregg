# Private large B admission timing

The exact 734,222-byte signed B call from the completed run-5 exchange was
submitted once to each of two independent private accepted-1 Store copies on
Persvati. No live or retained Store was opened for mutation. The accepted-1
preimage was reconstructed from the original pinned genesis and exact signed
birth call; its birth outcome matched run-5 byte for byte. The preimage SQLite
SHA-256 was `8eff8dd1c0a424ff75456da1adcc22c06774eab29238af001916b0a398404893`;
the signed call SHA-256 was
`59b6a3ac9a12a8552547833e1922ac7d3d9086ab1c26b404e10af3a9d60b952f`.
The two configurations differed only in private `storageRoot`.

| Linux host | SHA-256 | Elapsed | User CPU | Peak RSS | Approximate pre-write / post-write |
| --- | --- | ---: | ---: | ---: | --- |
| Selected bbf | `775a98c704e98b8a3065b2a93e9659aacf8f731f31d38b6360607e6bce64af19` | 456.94 s | 445.68 s | 1,721,276 KiB | 202 s / 254 s |
| Linear cSHAKE, before loaded-byte observation | `41647562c7dd1fe6cdf41836aa62c61fd7b24314f883b2bb14cb38779707c49a` | 201.13 s | 193.72 s | 1,723,952 KiB | 91 s / 110 s |

Both submissions exited successfully. Both produced the **same 132-byte
outcome**, SHA-256 `caf4009a43d3cd6f6773f971574a0b4c5597e716f4d04640b1f6b3c54d7c42ee`,
which also matches run-5, and byte-identical accepted-2 SQLite images, SHA-256
`0066f07fcfd6d92fd95717c809fbab173b74d45be604841bb8fc3899884d82a5`.
Thus this pair confirms a roughly 2.27-fold elapsed improvement on the same
large signed call and durable result. The new binary also includes later host
endpoints, though the inspected native submit, receiver, durable IO, and
observation modules were byte-identical between these two frozen sources; the
linear cSHAKE change is the relevant changed submit dependency.

The phase split uses the private SQLite file's modification time as the durable
write marker and the outcome file's modification time as the end marker. It is
an estimate, not an instrumented function-level profile. The linear run also
recorded explicit start/end timestamps. The old run's start is inferred from
`/usr/bin/time` elapsed and its end-file timestamp. The large post-write cost
is consistent with `NativeHost.confirmed` reopening and semantically replaying
the Store for exact historical receipt readback. In a persistent stdio session,
`Host.Main.sessionConfirmed` instead refreshes a verifier-minted tip and
`NativeHostReplay.extendVerified` checks the old prefix exactly, then admits
the newly appended suffix. At accepted 1 → 2, that suffix is this large call;
the one-shot post-write timing must not be presented as measured session cost.

The private pair was run with `/usr/bin/time -f
'elapsed=%e user=%U system=%S maxrss=%M'` around each host's `submit`
command, using the same call bytes and separate copied Store paths. No timeout
was changed. The combined linear-cSHAKE plus loaded-byte observation binary
`eddffd827496eb2a005af45158089957bacf63b019c8c3441b01b76b71db33b1`
has **not** been measured on this large call, so this evidence makes no latency
claim for the loaded-byte optimization.
