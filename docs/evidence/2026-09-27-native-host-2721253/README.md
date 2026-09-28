# Exact `2721253` typed birth readback candidate Host

This source-qualified Linux Host is a candidate for a **private copied-Store differential**, not a live deployment. It was built from exact committed Git archive `2721253`, SHA-256 `264c6e2ae6a28be42f83bc3f032ab11c17b85a0bf05b180cb43464fa805cb0fc`, in an independent writable copy of the certified `cb55b81` Host snapshot. Only `Kernel/NativeHostReplay.lean` SHA-256 `b79fec6992e600cfb0c8e307b25193b14eb5537dcb433260756e3a27d3313acd` and `Kernel/NativeHost.lean` SHA-256 `3f8a2828abde5e8d79963995b2625a03792750c995727f0d2cbedff5c3f8e697` changed in the 353-module production Lean closure. The extracted archive comparison showed only host UID/GID differences, no content differences.

The guarded suffix build validated 258 earlier module artifacts, 93 unchanged later sources, and 2,933 package objects against the certified `cb55b81` baseline. It compiled all 95 suffix Lean modules, including both changed modules and all dependents through `Host.Main`, then rebuilt native project C objects and linked a 3,286-object response. All 353 source SHA records and 9,831 reused-artifact SHA records passed independent post-build readback. The user unit `minidregg-2721253-host-r1.service` (invocation `f5621935d4224065a54e21925563241d`) terminated successfully after 394 seconds, with one serialized Lean compiler (`MINIDREGG_LEAN_THREADS=2`), two C jobs, CPU quota 200%, and memory cap 16 GiB.

Exact command from `/home/ember/build/minidregg-2721253-native-20260927`:

```sh
scripts/build-native-host.sh \
  --incremental-suffix-from \
  /home/ember/build/minidregg-cb55b81-native-20260927 \
  /home/ember/build/minidregg-cb55b81-evidence/build-r1 \
  Kernel.NativeHostReplay \
  --allow-suffix-change Kernel.NativeHost \
  --output /home/ember/build/minidregg-2721253-evidence/build-r1 \
  --binary /home/ember/build/minidregg-2721253-evidence/minidregg-host-2721253-r1
```

The ELF SHA-256 is `f62c716885d8f9258750da70113afc8d4086907a2cdbc1c11a8a5e3c5043bdcd` at the command's `--binary` path. A readback-identical mode-0500 copy is staged on hbox at `/tank/dregg-build/minidregg-2721253-host/bin/minidregg-host-2721253-r1`. The [manifest](manifest.txt) SHA-256 is `ad982d1ff97d352af38d1a1d8bbebebb3f5144d2c9b1737e5c0c11405ee45156`. Its inherited `git_head=791a6d2c...` denotes warm snapshot metadata; the committed archive and source readback determine provenance. `usage_exit=1` is the expected no-argument CLI usage result. The private physical birth differential and cold lookup are separate pending gates; this build alone does not establish runtime equivalence or a speed improvement.
