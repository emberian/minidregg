# Accepted lifetime grant inspection Host (2026-09-27)

Exact production Lean source cut: Mini commit `d48aa81`, with `Host/ApplicationAgentLifetimeGrantInspection.lean` SHA-256 `e04de72386e111300638c5fa62964c9178eddb5587ba8867454517547b1c7199` and `Host/Main.lean` SHA-256 `2e5a3d4c9a27bad6b5af2e30b758b0776ab507dc9115681075c3fb53f487422e`. The archived committed tree is `/home/ember/build/minidregg-d48aa81-source.tar` on Persvati, SHA-256 `1d032a4a60095ae28396b325c58ac5f7498edacb1c6251ee9de361645d990939`. All 353 closure source modules in the independent build snapshot matched that archive byte-for-byte; a recursive source-tree dry run (excluding only `.lake` and inherited `.git`) found zero differences. `git_head=791a6d2c` in the generated manifest is inherited warm-snapshot metadata, **not** code provenance.

The read-only warm baseline was the certified 9cd8c93 snapshot `/home/ember/build/minidregg-9cd8c93-native-20260927` and output `/home/ember/build/minidregg-9cd8c93-evidence/build-r1`. An independent writable copy received the exact d48aa81 archive before compilation. The guarded `--incremental-suffix-from` restart was `Host.ApplicationAgentLifetimeGrantInspection`, with `Host.Main` the only other declared changed source. This recompiles the dependent `Host.Json` even though its source is unchanged. Baseline/source/artifact checks accepted 328 reused prefix modules and 2,933 unchanged package objects; 25 suffix modules compiled with Lean 4.30 at two threads each, then C at two jobs. The final link used 3,286 response objects. No shared warm cache or live service was changed.

Build unit `minidregg-d48aa81-grant-host-r3.service` terminated successfully. The first two private attempts ended before compilation because the evidence directory and then the independent-snapshot marker were missing; their logs are retained in the private output and are not source failures. r3's 25/25 Lean suffix entries say PASS; source SHA readback passed 353/353, output artifact SHA readback 4/4, and reusable artifact SHA readback 10,211/10,211. The executable's usage probe exited 1, as expected for this CLI without arguments. This is a source/build qualification, not an accepted-event27 integration claim.

Qualified Linux ELF: `/home/ember/build/minidregg-d48aa81-evidence/minidregg-host-d48aa81-r3`, SHA-256 `674e70c22f1e5c7923aa6ef049ead473c959b0551e22f19e0ecbdd48cdf67cca`. Manifest SHA-256 `8c7aaa4306c4a7964b17202a26e6958961e932eb7c9c9f1a1165bea820590f2b`. A mode-0500 protected copy on hbox is `/tank/dregg-build/minidregg-d48aa81-host/bin/minidregg-host-d48aa81-r3`, read back with the same ELF hash. Source/build manifests and bounded validation, Lean, and link logs are adjacent to this note; the 10,211-entry reusable artifact inventory remains in the private Persvati output with SHA-256 `fde4440f5d89dd602450947774ac7ca7c882f02a867e145a1f354a95540c66b1`.

Build command (inside the independent source snapshot, with `MINIDREGG_LEAN_THREADS=2`, `MINIDREGG_NATIVE_JOBS=2`, CPU quota 200%, memory cap 16 GiB):

```sh
scripts/build-native-host.sh \
  --incremental-suffix-from \
  /home/ember/build/minidregg-9cd8c93-native-20260927 \
  /home/ember/build/minidregg-9cd8c93-evidence/build-r1 \
  Host.ApplicationAgentLifetimeGrantInspection \
  --allow-suffix-change Host.Main \
  --output /home/ember/build/minidregg-d48aa81-evidence/build-r3 \
  --binary /home/ember/build/minidregg-d48aa81-evidence/minidregg-host-d48aa81-r3
```

Native route verification remains open. A malformed-byte request on a private copy of the retained event22 Store hit a 180-second bound while opening/verifying history, before any success or rejection was returned; no output file was written. This is inconclusive, not a malformed-input rejection. A valid-but-absent candidate and an accepted event27 also remain pending a suitable canonical ingress fixture; no accepted grant was synthesized or inferred from this build.
