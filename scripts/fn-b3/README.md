# B3 synthetic fn reply handoff

These are test drivers for one isolated native owner and one already accepted
Mini E2 consumer operation. `mini_driver.py` reopens Mini's operation and Q,
stages the exact prepared and signed slots, proves a separate process can
reuse the signed slot with nonexistent private-key paths, then invokes fn's
native `hybrid-author`. `fn_owner_test.py` reopens the fn Store and verifies
the resulting `ARTICLE` through fn's native portable verifier, including exact
authored source, source identity, principal and full keyset. The shell bridge
only transports files and invokes the selected frozen fn image. None of these
scripts makes an application or Store semantic decision.

Run only against an isolated frozen fn gate. The fn owner fixture must be
started first; it atomically publishes `ready.json` and waits up to 900 seconds
for Mini's `mini-finished.json`. Both sides must use the same handoff directory.
For the 2026-09-24 retry, the qualified fn source is `e160442f`; the first
handoff was refused before signing because its source lacked Date. The fresh
handoff is under the same qualified gate with a distinct `retry-1` name:

```sh
cd /Users/ember/dev/minidregg-wt/fn-evidence
FN_B3_OUTPUT=/tmp/mini-fn-reply-plan-20260924/live-b3-retry-1 \
FN_B3_HANDOFF=/tank/fn/gates/luna-feature-e160442f/build/mini-b3-handoff-retry-1 \
FN_B3_MINI_HOST=/tmp/mini-b3-build-1eb84a9/build/minidregg-host-b3 \
FN_B3_MINI_CONFIG=/tmp/mini-fn-e2-native-20260923/live-deployment/pinned-config.json \
FN_B3_MINI_TRANSACTION=22678727908680307285286663340486134448208253926548865573615580900981947362607 \
FN_B3_MINI_REVISION=1eb84a9a46e08aa423a99e39ad74a9be538b5385 \
FN_B3_FN_REVISION=e160442f2a5401328f5e76c99216f0d11d5755cf \
python3 scripts/fn-b3/mini_driver.py
```

The fn gate copies `fn_owner_test.py` into its `tests/` directory and invokes
`tests.test_native_hybrid_b3_handoff.NativeB3Handoff.test_mini_reply_post_and_reopen`
with `FN_RUN_HYBRID_E2E=1`, `FN_NATIVE_HOST` set to the gate's frozen image,
`FN_TEST_OPENSSL` set to OpenSSL 3.5.8, and `FN_B3_HANDOFF_DIR` set to the path
above. Preserve the exact command, image hash, test file hash and raw log. The
driver's `evidence.json` records source and artifact hashes; the prepared and
signed SQLite roots and readback files remain under `FN_B3_OUTPUT`.

The `8c61c098` combined topic/index gate exposed proof regressions before an
image was built. This B3 fixture uses the earlier qualified `e160442f` image;
its result carries no topic/index claim.

`forge_history.lean` is a separate scratch-only negative replay tooth for a
later Mini host change. Set `MINI_B3_FORGE_CONFIG` to an existing pinned Mini
config and `MINI_B3_FORGE_OUTPUT` to a fresh absolute file, then run
`lake env lean scripts/fn-b3/forge_history.lean` against compiled current
modules. It writes a physically restorable copy with the first original
ingress changed to `[255]`; install only into a scratch SQLite root and run
the candidate host's `describe` against a config selecting that scratch root.
The expected result is a semantic-history refusal with no Store mutation.

This fixture does not exercise a lost fn post reply, an uncertain post lookup,
a second administered Store, or power loss. Do not extend its claim to those
boundaries. The Mini executable's code is at `1eb84a9`; the prior `9c1bb384`
executable lacks Date and was refused before signing. The Date repair also
changed the Message-ID domain to v2, so the fresh slot cannot reuse v1 bytes.
