# Composite birth authoring and stable fn binding image (2026-09-27 UTC)

These Mac and Linux images derive from the immutable [181-module first
composite build](../2026-09-26-mini-provider-composite/README.md). The only
source changes in the native import closure are committed `Host.Json` SHA-256
`31f400a1d483e0e9fb400fd5a2790f0cfdb497dc5ab9b4f6a2d989a22d863a06`
(`f608c3b`) and `Host.Main` SHA-256
`d5daf1d78f23a81fee30e42f9c95ad5d9574b36cdbe8282429ce38c3faa2e95d`
(`2b6db7d`). `Host.Json` can author a later-height bare birth from an explicit
signed challenge height; omitted height retains the genesis behavior.
`Host.Main` binds fn control to the stable configured binary path.

Each guarded suffix build revalidated 173 earlier source/Lean artifacts, six
unchanged later sources, 2,933 package modules, the baseline binary, and the
toolchain. It compiled the eight-module `Host.Json` through `Host.Main`
suffix, linked 3,114 response objects, and rechecked all 181 source modules
and four recorded output artifacts. The Mac and Linux source manifests are
byte-identical, SHA-256
`6a819c8125c5c78031b438beb4592281781b0c974d5338250e06514f0757e7ea`.
The no-argument `usage_exit=1` is expected.

The Mac executable is
`/tmp/minidregg-overnight-20260926/minidregg-host-provider-composite-height-stable`,
SHA-256 `1092a5bc29e3811bd9183b207ca5aa6e25ac9e1bc2895bfc5af92c89cd04165e`.
The Linux executable is
`/home/ember/build/minidregg-overnight-20260926/evidence/minidregg-host-provider-composite-height-stable`,
SHA-256 `30731bb4e35b784ab58fa8f442407ef2bc4fddeed77ab782a5056f107096fc82`.
The [Mac](mac-manifest.txt) and [Linux](linux-manifest.txt) manifests record
their exact source roots and build parameters; adjacent source/artifact and
incremental-validation files record the guard results.

This certifies source and native build provenance. The fresh isolated signed
grain-birth r3 fixture and fresh fn A gate are separate runtime evidence;
neither live deployment nor acceptance is inferred here.
