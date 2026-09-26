# Persistent native replay probe

Run `replay-poison.sh HOST MINI STORE SIGNATURE-HELPER NEW_ROOT` with exact-source
binaries and a new scratch directory. The driver runs the existing resource
client acceptance journey with three native image captures, then uses the
store's exact-byte CAS to replace a live host's verified image with (1) a valid
older prefix and (2) a distinct valid image at the same height. The Rust stdio
probe requires the first `describe` frame to succeed and all frames after each
replacement to fail. A fresh cold host must open each image before the fork
swap. `NEW_ROOT` retains logs, source intents, images, binary hashes, and
acceptance evidence. Its generated custody key is private; do not publish the
directory as a public artifact.

This exercises native receiving and process behavior for these exact binaries.
It does not prove arbitrary history or storage correctness.
