# Verified historical app share issue selector

`Kernel/ApplicationShareIssueHistorical.lean` SHA-256
`c1ae4be48b528f37a654c49b815386c1892508383902fb0505d6efdd35a05576`
compiled without diagnostics against a coherent private Mini snapshot with
committed `Kernel/NativeHostReplay.lean` SHA-256
`1c4522541e1bd9092f83606c1d3f65b4429697f2decd7ccbf302163b03fd76f7` and its matching OLean SHA-256
`a2079b41c1b120193d39c794ab723ab4617c67bed0fcdcf8f06c779d2962bce9`.
The snapshot source was later changed by a separate uncompiled replay-context
draft; the direct check imported the pinned OLean above, not those later bytes.
The direct command was:

```sh
cd /home/ember/build/minidregg-overnight-20260927-selected-prefix-codec
LEAN_NUM_THREADS=2 /home/ember/.elan/bin/lake env lean \
  /tmp/minidregg-shareissue-historical-575ee898.lean
```

That first source SHA `575ee898…` proved the exact verifier-selected-prefix
re-admission and full record equality. The final source above adds only
`Issued.toEvidence`, passing the already proved full record equality into
`ApplicationDispatchHistoricalCore.IssuedEvidence.fromAccepted`. It and the
dependent dispatch Upper module compiled serially with exit 0 in the separate
private snapshot `/home/ember/build/minidregg-dispatch-upper-20260927-spkcompat`.

The selector calls `verifyLoadedSelected`, re-admits issue event 15 against
the **actual selected prior image from the native replay walk**, compares the
complete `IntentRecord`, and retains the original verified receipt. It is a
source-only proof/API checkpoint. It has not yet linked into a native dispatch
receiver, admitted a dispatch, or authorized physical app delivery.
