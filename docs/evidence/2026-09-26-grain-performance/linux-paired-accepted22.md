# Paired Linux observation timing at accepted 22

The source Store was quiet after the parent settle at 06:19:47 EDT. A SQLite
online backup made at 06:21:01 EDT captured **accepted 22**, not accepted 20.
The sealed backup and the benchmark's private copy both have SHA-256
`1c3a45101b68500a069db8ed575156c9a5f319b86c73b35b900023c70a9d4302`.
Neither host opened the live Store or socket. The benchmark configuration
changed only `storageRoot` to that private copy (SHA-256
`a1f0447a6d1ddbf370d278e322046c323522ac57d023eb9b28b65bfff80b52b0`).

The cap-94 object-7003 signed query was freshly prepared against the copied
accepted-22 tip. Its intent, signed observation, challenge, and view SHA-256
values are `504507ec65ac08d40643f3c60d984d723f211e494a2e226c0bc9369c90a90fc7`,
`93ad4ec1d14ab01d181461cda307644825008ac7ef68f918c57ada0e4dd1fec3`,
`25322061fffb06d9130841f3ef526dc951a0ac8d04528ecc071871d6b9a15b36`,
and `352cfe44ea7a68409a363ecb9775d541f73ec2b07735aabb36bee6bdbb8f0f05`.
An earlier accepted-20 query was discarded before this measurement.

| Linux host | Cold describe | Warm describe | Challenges (s) | Signed queries (s) |
| --- | ---: | ---: | --- | --- |
| Old `faf1f8371f692c404acd5b4c5727bd2019249c1b5f7d1850022789d35f4ee30f` | 180.352 s | 1.426 s | 11.122, 11.187, 10.714 | 33.721, 26.481, 24.803 |
| Combined `31a00492594a9abbde4541fef687f4d6a2fd2cac06c1645e604178a3e7f18179` | 169.688 s | 0.029 s | 4.768, 3.345, 3.444 | 7.111, 7.499, 8.375 |
| Linear CShake, pre-loaded-byte `41647562c7dd1fe6cdf41836aa62c61fd7b24314f883b2bb14cb38779707c49a` | 166.516 s | 0.025 s | 2.804, 2.931, 2.871 | 7.414, 6.360, 6.800 |

All eight framed responses have identical opcode and SHA-256 between hosts;
all three challenges and queries also match the freshly recorded exact bytes.
The complete per-call records are
[old](linux-old-accepted22.jsonl) and
[combined](linux-combined-accepted22.jsonl). A third
[linear-CShake run](linux-linear-accepted22.jsonl), SHA-256
`a8a343648b147298e04d1b8ea53aeccc18f294d1193c419862d10cce1bd73548`,
used the same sealed backup, copied configuration, signed query, and driver.
It includes the proven linear absorber and later op17/18 endpoints, but not
commit `83ba61e`'s loaded-byte observation change. Its eight framed response
bytes match the combined image; every challenge and query also matches the
recorded source bytes. All records were generated with
[the benchmark driver](bench-grain-observation.py). This is a sequential,
wall-clock comparison on Persvati under ambient load, not an isolated CPU
microbenchmark. The combined observation/session path cuts warm challenge
and query latency substantially, while cold semantic replay remains near
three minutes at this history size. Linear CShake gives a smaller gain on
this short signed query; these runs do not measure a large payload admission.
