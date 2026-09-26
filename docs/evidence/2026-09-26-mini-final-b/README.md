# Mini B native host build (2026-09-26)

This evidence records the source-matched Mac arm64 Mini host for B opcodes 12/13. The native executable is `/tmp/minidregg-overnight-20260926/minidregg-host-final-b-fast`, SHA-256 `c2a1fd3699338f28eaf1d076b53cbd1bf27b4438b857b0482666205b334a394c`.

The frozen build source is commit `591a5a91252846d1ffca51e8bf87524d7027a20d` for every build-relevant Lean file, plus the `Kernel/AgentGrainAudit.lean` repair committed at `3744eb268a321766ad10abb3c1f32f4fdc147b03`. The clone's Git HEAD is older because ten exact files were overlaid; [source-manifest.txt](source-manifest.txt) and [overlay-sha256.txt](overlay-sha256.txt) make that provenance explicit. Foreign `Compiler.lean` work and later A opcodes 14/15 are excluded.

`Host.Main` leanArts compiled all 162 required source modules; the native link used 2,933 pinned package objects and 3,095 total response objects. The executable printed its usage contract, and all 162 source hashes still matched after the build. The separate full `Minidregg` umbrella gate and independent runtime acceptance were pending when this build record was written; their verdicts must be added before treating it as a complete release gate. No private store, key, signed call, or live fn image is included here.

The same frozen source linked on persvati as an ELF x86_64 executable at `/home/ember/build/minidregg-overnight-20260926/evidence/minidregg-host-final-b-fast`, SHA-256 `faf1f8371f692c404acd5b4c5727bd2019249c1b5f7d1850022789d35f4ee30f`. Its independent package tree had no writable symlinks. The Linux Host.Main gate, C/link, usage contract, and 162 source hashes passed. See [linux-build-manifest.txt](linux-build-manifest.txt) and [linux-source-verify.log](linux-source-verify.log).
