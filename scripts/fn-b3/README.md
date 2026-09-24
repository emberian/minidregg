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
started first; it atomically publishes `ready.json` and waits up to 600 seconds
for Mini's `mini-finished.json`. Both sides must use the same handoff directory.
For the 2026-09-24 campaign, set `FN_B3_GATE` to the actual qualified fn
gate path and `FN_B3_QUALIFIED_FN_REVISION` to its exact source revision.
The handoff is `<qualified-fn-gate>/build/mini-b3-handoff`. The Mini side is:

```sh
cd /Users/ember/dev/minidregg-wt/fn-evidence
FN_B3_OUTPUT=/tmp/mini-fn-reply-plan-20260924/live-b3 \
FN_B3_HANDOFF="$FN_B3_GATE/build/mini-b3-handoff" \
FN_B3_MINI_HOST=/tmp/mini-b3-build-9c1bb384/build/minidregg-host-b3 \
FN_B3_MINI_CONFIG=/tmp/mini-fn-e2-native-20260923/live-deployment/pinned-config.json \
FN_B3_MINI_TRANSACTION=22678727908680307285286663340486134448208253926548865573615580900981947362607 \
FN_B3_MINI_REVISION=9c1bb384c562826733388b6ac0ce55950c070a88 \
FN_B3_FN_REVISION="$FN_B3_QUALIFIED_FN_REVISION" \
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
image was built. The B3 reply fixture can use the earlier fully qualified
`e160442f` image if its hybrid sign/post/readback interface matches; record
that older image's exact source and limit the claim to B3 behavior on it.

This fixture does not exercise a lost fn post reply, an uncertain post lookup,
a second administered Store, or power loss. Do not extend its claim to those
boundaries. The Mini executable's code is at `9c1bb384`; the subsequent
`29ffea5` commit corrected only this protocol's documentation.
