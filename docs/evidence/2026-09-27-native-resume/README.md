# Guarded failed-build resume (2026-09-27)

`scripts/build-native-host.sh` SHA-256
`f266abfed8f86460989ae04aaf9dcab8cc9bc953a2d27c5d6f06031c1ee8416b`
adds opt-in `--checkpoint-resume` for full non-umbrella builds and
`--resume-failed BUILD_OUTPUT` in the same independent source snapshot.
Ordinary builds do not pay the cost of hashing Lean's library trees.

The checkpoint contract records the exact Host.Main import closure, project
and package module lists, Lake/toolchain inputs, all regular files in the
toolchain and package Lean-library trees, and toolchain symlink targets.
Nested package symlinks are refused. Each successful project module gets an
atomic SHA-256 checkpoint for its source and every matching generated artifact
in its Lean library and IR directories, including OLean companions, hash
sidecars, generated C, and any existing object. A resume requires a recorded
Lean failure, identical closure/input lists, verified external inputs, and a
consecutive unchanged prefix. It recompiles the remaining modules and all
project C objects. Failed outputs without this contract are refused.

In an APFS copy of the 187-module application-birth snapshot, a deliberate
test-only syntax error in `Compiler/Air.lean` made the initial build stop at
module 3 after modules 1 and 2 passed. The [resume log](resume-build.log)
shows the two-module prefix accepted, no recompilation of those two modules,
and the same module-3 failure. This is a validation of guarded prefix reuse,
not a completed native link. The initial [failed build log](failed-build.log)
and [module-1 checkpoint](prefix-checkpoint-0001.sha256) retain the bounded
details. The external input manifest had SHA-256
`91f688b52823094c7c3c9b0a38c76244dc5832716cb8e6caa5422e472c0941e7`.

Private negative runs on the earlier, narrower draft refused with exit 65
before Lean compilation when the completed prefix source, its `.olean`, or a
package `.olean` changed. The final broadened contract refused a changed
`Pred/Core.olean.hash`
auxiliary artifact with exit 65; see the [captured log](changed-auxiliary.log).
An inserted nested package symlink was also refused with exit 65 before
hashing or compilation; see the [symlink log](nested-package-symlink.log).
All deliberate mutations were confined to the private copy and restored;
the [prefix restore check](restored-prefix.log) is green. The certified
application-birth Host and its source snapshot were not modified.

`bash -n`, `shellcheck`, and `git diff --check` passed on the final script.
A focused path-set check for a slashless top-level module included its
source, public/private OLeans, ILean, and generated C from the correct
top-level artifact directories. The earlier large private resume tests used
the same checkpoint contract before that path-only correction.
The full 187-module native link has **not** been rerun with resume mode; the
existing certified build remains the source-matched native artifact for the
application-birth fixture.
