# sntfy signed root-prefix SPK qualification (2026-09-28)

This is an isolated second-profile qualification, not a Mini INSTALL or resident
lifecycle completion. No sntfy executable or live service was started.

The input is the retained Sandstorm catalog package
`/tmp/spk-mini-probe/sntfy.spk`, SHA-256
`bc424d5fd3cf60977cacdac328adfbee4de94f88d57383ad38b3d472c0c24f2d`
(17,379,772 bytes), previously inventoried in
[`../2026-09-27-spk-app-selection/README.md`](../2026-09-27-spk-app-selection/README.md).
The same bytes were copied to isolated hbox scratch
`/tank/dregg-build/api-path-check-20260928/sntfy.spk`; SHA-256 matched after
copy. The updated native `spk-host qualify` parsed and verified those bytes with
Bread's SPK signature, archive and manifest parser. Its exact JSON output is
[`signed-qualify.json`](signed-qualify.json). The source descriptor JSON
[`source-descriptor.json`](source-descriptor.json) selects only values from that
verified parse; it is not an asserted package identity.

The signed bridge declares API prefix `/`, permission names `admin` and
`fullapi`, and an API role with `fullapi`. The signed app ID is
`c6rk81r4qk6dm3k04x1kxmyccqewhh4npuxeyg1xrpfypn2ddy0h`, version 18.
Native `spk-host materialize` succeeded into the fresh, protected
`/home/hbox/sntfy-gateb-20260928/packages/sha256-bc424d5fd3cf60977cacdac328adfbee4de94f88d57383ad38b3d472c0c24f2d`
directory using app UID 65534. [`installed-inspection.json`](installed-inspection.json)
records `inspect-installed` reparsing the stored
signed package and matched the raw SHA-256, 17,379,772-byte length, app ID,
version 18, signed manifest SHA-256
`7ebb802cc26dd490ec6812983847faeb735d3e6fcee847e7d53ef603433e1e79`,
and signed bridge SHA-256
`1a5fb4c75adda3647c6f9bfc3101190084ac82e21412bfd1fd4fb093a16938ee`.
The materializer's [`signed-manifest-projection.json`](signed-manifest-projection.json)
retains the decoded create/continue commands from that verified archive.

The native executable came from the isolated hbox checkout
`/tank/dregg-build/api-path-check-20260928/native/spk-host` with
`CARGO_BUILD_JOBS=2 cargo build --bin spk-host`. The source-owned Lean descriptor
author/inspect and the lifecycle admission/runtime checks are separate steps;
their evidence must be added before claiming a complete non-Git Gate B.
The native executable SHA-256 was
`98ea9203707b9fae7f959aba5d7168644d1f3af957acb5eff4a8052b127588ef`.
It was rebuilt after the final shared signed API path bound landed; the
`qualify` and `inspect-installed` JSON from that executable matched the
captured files byte for byte. The checked Rust source SHA-256 values were
`native/spk-host/src/main.rs = 073705af9726e0695d95740135ec000fc0e815aae6b0ced93d186be194231800`,
`native/spk-host/src/materialize.rs = 1340cb6c3400f7d3c9f8be2a50567b9cea52054526c6f24c2967d3925b1dc959`,
and `native/signed-api-path/src/lib.rs = 9b6d3c35a7fa41bd326ef9c94439a78454b4b08579904b921c48a25ee9394bcc`.
The offline source-join adapter hashes also matched the shared tree:
`native/spk-host/src/descriptor_native.rs = ec3f54e4507139a65cc5833c5fe16c7da7a0f51c2ba72c3b20f9a6c51a2a0ec2`
and `native/spk-host/src/launch_descriptor_native.rs = e0ed2ca762d3e0cd7454645ae9c8c6b58922db7ad799568792a66f9e98afcd21`.
The future source CLI roundtrip uses [`authoring-config.json`](authoring-config.json)
only to satisfy the host's startup settings parser; all storage and verifier
paths are intentionally nonexistent because descriptor author/inspect is pure.

The source descriptor selection was:

```sh
jq '{rawSha256,rawLength,signedAppId,signedAppVersion,manifestSha256,bridgeConfigSha256,bridgeApiPath,signedSchema}' signed-qualify.json > source-descriptor.json
```

The retained GitWeb source input
[`legacy-gitweb-source-descriptor.json`](legacy-gitweb-source-descriptor.json)
comes from the earlier verified GitWeb package and signed schema, and checks
that this new source host still emits its historical v1 descriptor bytes.

The new source `Host.Json` directly passed a Lean author/inspect roundtrip in
a private, source-matched OLean overlay with [`ProbeDescriptor.lean`](ProbeDescriptor.lean).
The sntfy package produced
[`sntfy-package-identity.bin`](sntfy-package-identity.bin) SHA-256
`673dade8648d1e3b070766a6363cf10bab1624fa5ac6a6486c54eadfdfb777e1`;
[`sntfy-package-inspection.json`](sntfy-package-inspection.json) reports type
`application-spk-package-identity-v2`, exact signed API path hex `2f`, and
root `54038320703104217148301107210384541973782719759286932651188781042642979250281`.
The retained GitWeb input produced
[`gitweb-package-identity.bin`](gitweb-package-identity.bin) SHA-256
`a853b57cb79ce72f965d97b682a17c83e1396ef8e8f2f65d130e3207dbec7e7f`,
identical to its historical v1 bytes; its
[`gitweb-package-inspection.json`](gitweb-package-inspection.json) reports
`application-spk-package-identity-v1` and the historical root.

That Lean check used the source-matched `Host/Json.lean` SHA-256
`23f3937a00dd78e044cb77c88e84271fbaca6c1c20e54894952511650a753925`
and the private overlay at
`/home/ember/build/minidregg-recovery-20260928/source-api-kernel/lib` on
Persvati. It does not substitute for the linked native Host CLI or a Mini
lifecycle operation.
The source profile SHA-256 values were
`Kernel/ApplicationSpkPackageIdentity.lean = 982982dca5c7aa696164c420305a0cd25a2d6e82cc4d6bcb8781840f24814373`,
`Kernel/ApplicationSpkLaunchDescriptor.lean = 98111517e43621c7ff416c1931e1dd5031b9aa565a89bf30d99fda5fbba458eb`,
and `Host/ApplicationSpkLaunchDescriptorAuthoring.lean = 8000daefc9add22c392707895b56bd0bd9907a48c90bfaf9a7a1b313563df5ba`.

The verified installed manifest's create and continue commands were projected
with [`make-launch-source.py`](make-launch-source.py) into
[`sntfy-launch-source.json`](sntfy-launch-source.json), containing the exact
ordered argv and environment bytes plus the already source-authored package
identity. [`ProbeLaunch.lean`](ProbeLaunch.lean) then used the same source
`Host.Json.author/inspect` route. Its
[`sntfy-launch-descriptor.bin`](sntfy-launch-descriptor.bin) SHA-256 is
`fcdabc197819c887328aa4e330ca5ada36dbe6a4f11a65a0be6dd6620bf8a11a`.
[`sntfy-launch-inspection.json`](sntfy-launch-inspection.json) reports
`application-spk-launch-descriptor-v3`, the same package root
`54038320703104217148301107210384541973782719759286932651188781042642979250281`,
and launch root
`67784406165915398171253729794221377341696044825809329388824055606148431998635`.

The linked Linux Mini Host later qualified at SHA-256
`723940446d3e0256bd446b07ca8d67ea9d67295d8c7cc78e08bb2487ffbe3db2`
(the guarded e22d16b r3 build, all 363 Lean modules passed). It was copied
byte-for-byte to the isolated hbox fixture and pinned there with the inert
config SHA-256
`b505b4554a756d65d8a90a698570c76117eb7d6f12e42eac2f741f6a081669f9`.
The native `spk-host qualify-launch` path reparsed the signed sntfy SPK once,
asked that exact Host to author/inspect its schema, package identity and launch
commands, and compared the source output with the signed physical parse.
[`native-qualification-config.json`](native-qualification-config.json) is the
exact pinned input (SHA-256
`a09ecd2d54f98c3d2e745c4a8a78880a63f6874ff84a48c6a4128632e912c514`);
[`native-qualification.json`](native-qualification.json) is the retained
successful result. Its native-produced package and launch descriptor SHA-256
values were exactly the direct Lean values above. The result reported one
create command and matching create/continue digest
`23712759354380648489357541318694824213814556795961007356763671526226534484272`.
The same qualified linked Host also authored and inspected the retained GitWeb
source input through its CLI on Persvati: canonical bytes and inspection were
byte-identical to the direct Lean artifacts above, preserving v1 type, root
and SHA-256 `a853b57cb79ce72f965d97b682a17c83e1396ef8e8f2f65d130e3207dbec7e7f`.
This remains a pre-Store qualification: no Mini INSTALL, resident START/STOP,
agent request or sntfy process was executed.
