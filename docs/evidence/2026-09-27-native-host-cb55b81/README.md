# Exact `cb55b81` multi-provider native Host

The Linux Host was built from the exact committed Git archive `cb55b81`, SHA-256 `2e59a86c1780b49897cdcb631b1cf518a58b4df87aa9b35101ca216261805927`, in an independent writable copy of the certified 8c13 snapshot. Only `Host/ProviderUsage.lean` (`ca41d991dcae2e3350b3ea705144bcdae1279308e9c7b59a183578c303621854`) and `Host/Main.lean` (`36cccb3bd6bccc88b4d0c218e590063b8dcb49e7ad436d102582a68c8f6a346d`) changed in the 353-module production Lean closure. The guarded suffix validator checked 351 reused modules and 2,933 package objects, compiled both changed modules (8 s and 43 s), rebuilt project C objects, and linked a response with 3,286 objects. Source SHA readback passed 353/353; reusable artifact readback passed 10,203/10,203. Archive comparison after the build found only host UID/GID metadata differences, no content differences. The manifest's inherited `git_head=791a6d2c...` identifies warm-cache metadata, not source provenance.

The bounded Persvati **user** unit `minidregg-cb55b81-host-r1.service` (invocation `adf5deeee89543beb84949519608f89b`) terminated successfully after 315 seconds. It ran with `MINIDREGG_LEAN_THREADS=2`, `MINIDREGG_NATIVE_JOBS=2`, CPU quota 200%, and memory cap 16 GiB. Exact command from `/home/ember/build/minidregg-cb55b81-native-20260927`:

```sh
scripts/build-native-host.sh \
  --incremental-suffix-from \
  /home/ember/build/minidregg-8c13c42-native-20260927 \
  /home/ember/build/minidregg-8c13c42-evidence/build-r1 \
  Host.ProviderUsage \
  --allow-suffix-change Host.Main \
  --output /home/ember/build/minidregg-cb55b81-evidence/build-r1 \
  --binary /home/ember/build/minidregg-cb55b81-evidence/minidregg-host-cb55b81-r1
```

The ELF SHA-256 is `89973efe154b3f53bb279a931a93aed0b0a1d341d759dc776dca635dda01c354`; the source-matched Persvati path is the command's `--binary`, and a readback-identical mode-0500 hbox copy is `/tank/dregg-build/minidregg-cb55b81-host/bin/minidregg-host-cb55b81-r1`. The [manifest](manifest.txt) SHA-256 is `47f6633e5835e312f9487693c158001af9937668e1f1c8117f1f25285f4c32b4`. Its `usage_exit=1` is the expected no-argument CLI usage probe. The adjacent build, validation, source, and link records document the complete artifact qualification.

Read-only native `profile` checks used private copies of the earlier provider fixture configuration and Store. The legacy scalar pin emitted only `providerMetering` for resource 7204. A two-entry service list emitted only `providerMeterings` for resources 7204 and 7205, both with the same operator tariff digest as the old scalar fixture. Mixed scalar/list settings refused with `providerServices cannot be combined with legacy provider pins`; duplicate 7204 IDs refused with `providerServices resource IDs must be positive and unique`; an empty list refused with `providerServices requires one to eight entries`. The separate hbox Bonsai candidate configuration SHA-256 `0af8e942...` parsed read-only with service IDs 7950 and 7951, model `bonsai2-27b-ptq1`, zero rates, and no scalar metering pin.

Actual op19 v2 quote checks used the exact `cb55b81` Host and Mini against a separate 624 KiB copied Store. The historical retained 36 KiB request and synthetic complete SSE response stayed private; no upstream send occurred. Strict v2 metadata selected provider 7204 and then 7205 in two independent attempts. Both returned `quoted-reported-usage`, charge 3, and a source-authored `settle` operation for charge 3; [7204](v2-7204-meter.json) and [7205](v2-7205-meter.json) are the bounded typed outputs. Raw reply-frame SHA-256 values were `3bbfa6e53aa4bc2b4e6af210bbb952be0dbd0ff6377a53f54030c04d0686e44a` and `2e00919903a7cb78a40bfdc4947f7bd6377c0cc501870e805698b32532be8fec`. Both scripts compared all copied Store file hashes before and after and found them equal; a final post-shutdown inventory also matched the original, SHA-256 `e3a966dd98c25d75b6ecb65690c9ee6a3b57afd3d5d606b803f82d23374f81f2`. These quotes report provider usage under the pinned tariff; they do not attest an invoice or perform settlement. No live r3 Store or service was changed.
