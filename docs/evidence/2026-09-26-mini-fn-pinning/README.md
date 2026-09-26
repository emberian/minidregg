# Mini fn helper pinning: isolated runtime probes

Host/Main.lean source SHA-256: `82c7f9d1bc5ddd64c8ed354a3e0ee1fce5aed3b1fd634e446eef418e7bf3e900`.

The host module compiled to OLean/C in the exclusive receiver snapshot with `LEAN_NUM_THREADS=2` and Lean exit 0. The two probes import that exact Host.Main OLean, run in the same isolated snapshot, and pass:

- `probe-fn-helper-snapshot.lean`: after the configured local executable file is rewritten, the private copy still executes the original bytes. This checks the local helper copy; it does not pin a remote fn image selected by the bridge.
- `probe-fn-pin-json.lean`: an existing five-field fn pin JSON still parses; the private execution/key paths can change without changing the logical `fnBinary` and `mlPublicKey` fields used by durable binding.

Logs: `helper-pathswap.log`, `fn-pin-json.log`. This evidence is narrower than a linked stdio or fn Store acceptance run. The remote `FN_B3_IMAGE` remains an operator-qualified custody dependency.
