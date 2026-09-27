# Successful native-build prefix reuse

The new `--reuse-success-prefix-from SNAPSHOT BUILD_OUTPUT` mode takes a separate, successful `--checkpoint-resume` build as its baseline. It verifies the baseline executable and anchored source/artifact manifests, the exact external toolchain and package inputs, the current project's topological import order, and every source and generated artifact in the reusable prefix. The first changed or inserted module starts a fully recompiled Lean and project C suffix. An unchanged source with changed generated output is refused. Project source bytes are captured before compile and rechecked at successful link.

The baseline must itself have been built with this script revision and `--checkpoint-resume`, which writes a `checkpointed_success=1` manifest and anchors final post-link module checkpoints. Legacy successful builds without those checkpoints are intentionally refused. This is a source/artifact reuse qualification; a full native integration run with a new checkpointed baseline has not yet been performed.

The isolated fixture invokes the production prefix selector on three fake modules. It checks identical reuse, changed dependency and later-source suffix boundaries, insertion, altered private OLean bytes, and an optional generated-artifact symlink. It does not invoke Lean or the native linker.

Validation: `bash -n` and `shellcheck` on the builder and fixture, the fixture itself, and `git diff --check` all passed. Exact outputs and hashes are in `validation.log`. No running build snapshot was modified.
