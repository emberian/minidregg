# Proved UInt64 Keccak permutation and matched native admission

The committed `Compiler/Sp800185Cshake256Core.lean` at `b609133` keeps the
original `keccakF1600 : Array (BitVec 64) → Array (BitVec 64)` definition and
adds a UInt64 implementation plus the general `@[csimp]` theorem
`keccakF1600_eqUInt64`. The theorem covers **every** input array, including
empty and short arrays with the reference implementation's default lane. It
commutes lane lookup, column parity, cached theta, rho/pi, chi, round, and the
entire round-constant fold. The rotation lemma covers every natural-number
offset, including zero modulo 64. `#print axioms` reports only `propext`,
`Classical.choice`, and `Quot.sound`; no finite-vector check or FFI establishes
equivalence.

The Core source SHA-256 is
`aa4e9294eab4243590a51b3ecfbb54c7e613f6807a37b055800cc649437949c0`.
`LEAN_NUM_THREADS=2 lake env lean Compiler/Sp800185Cshake256Core.lean` passed.
Compiling the same Core to C (`lake env lean -c`) produced SHA-256
`2d176d368e80080df8ef5bcb351e6ae0ed04701d61690830216aac0df51d0aff`.
The bounded [generated-C call graph](generated-c-callgraph.txt) shows both
`absorbPaddedIndexed` and `absorbFrom` calling the UInt64 permutation. Its hot
round uses native `uint64_t` bitwise and shift operations. The original BitVec
reference functions and a proof-only rho/pi helper are also emitted as C;
their presence is not evidence that absorption calls them.

An independent private overlay of the changed Core passed the existing NIST
SP 800-185 cSHAKE sample 3 and FIPS 202 empty SHAKE256 checks. A separate
4-byte input and 301-byte multi-rate customized input produced byte-identical
32-byte results against a separately compiled committed pre-change Core
(SHA-256 `c4c8aa4b7cf7b61817803426d728a8a6e51321a3b0d96042117d190b8aae0ba0`).
The two output files both hash to
`522f58db97a6cdec02ef809f646be2b1ed95f33a378e0b1f96868e8e090ddb46`.
These vectors are regression checks; the general theorem supplies equivalence.

The Linux native Host was built from an independent copy of the certified
`source-final-combined` snapshot, with **only Core source** changed. The
incremental build verified 53 earlier modules, 115 unchanged later sources,
2,933 package objects, and compiled the 116-module suffix. Its
[captured manifest](linux-host-manifest.txt)
has SHA-256
`9ed4d3653331588f138acc1a619944098984225277c80d5aba79feae0e250f56`;
the resulting binary SHA-256 is
`e421064bd30bcaab7e4db8779a6117f07c02414633cd712ac53f37e85a9ba186`.
The build ran with two Lean threads, two C jobs, and a 64 GiB systemd memory
limit. This snapshot deliberately excludes concurrent NativeHost/DRC work.
The bounded build invoked `scripts/build-native-host.sh
--incremental-suffix-from BASE_SOURCE BASE_OUTPUT
Compiler.Sp800185Cshake256Core --output OUTPUT --binary BINARY` with
`MINIDREGG_LEAN_THREADS=2` and `MINIDREGG_NATIVE_JOBS=2`; the captured manifest
records the resolved source, output, and binary paths.

The separately qualified macOS Host used an APFS copy of the certified
`minidregg-overnight-20260926-combined` source, again changing only the same
Core file (verified by content comparison). All 169 Lean modules passed, the
116-module suffix linked, and the incremental source/artifact checks passed.
Its [captured manifest](mac-host-manifest.txt) has SHA-256
`f61ffb4e06b0fb0beced34b696445d173dad1db9a1326372c6c5890d52e4b516`;
the Host binary `/tmp/minidregg-overnight-20260926/minidregg-host-u64-b609`
has SHA-256
`49e8e6f05fd1f86c88e8920e66e3827b6a026bb265bd305e4438bc1fb2e4ed41`.
This binary was handed to the pending content-B recovery owner for exact
read-only lookup; this lane did not access that Store.

The same 734,222-byte signed call (SHA-256
`59b6a3ac9a12a8552547833e1922ac7d3d9086ab1c26b404e10af3a9d60b952f`)
was submitted one-shot against a **fresh copy** of the sealed accepted-one
SQLite pre-state (SHA-256
`8eff8dd1c0a424ff75456da1adcc22c06774eab29238af001916b0a398404893`).
The UInt64 Host returned the exact baseline outcome SHA-256
`caf4009a43d3cd6f6773f971574a0b4c5597e716f4d04640b1f6b3c54d7c42ee`
and post-state SQLite SHA-256
`0066f07fcfd6d92fd95717c809fbab173b74d45be604841bb8fc3899884d82a5`.
The one-shot invocation was `HOST CONFIG submit CALL.bin OUTCOME.bin`, where
`CONFIG.storageRoot` pointed at the fresh private copy of the sealed pre-state.

| One-shot Host, same call/pre-state | Elapsed | User CPU | System CPU | Max RSS (KiB) |
| --- | ---: | ---: | ---: | ---: |
| Certified BitVec baseline | 189.68 s | 183.43 s | 6.14 s | 1,391,948 |
| Core-only UInt64 Host | 35.76 s | 30.78 s | 4.94 s | 1,380,848 |

This is a 5.30× wall-time improvement in one matched run. The exact outcome
and post-state hashes establish the same accepted transition; timings can
still vary with host load. The private measured Store is
`/tmp/minidregg-large-b-profile-20260926/u64-b609-one-shot` on persvati.
The [captured timing](linux-large-b-one-shot.time) is from that one-shot call.
