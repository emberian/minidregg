# Exact append operation proof

`mini operation-proof --dir WORKSPACE --operation-record ABS_FILE --socket SOCKET`
returns one `minidregg-append-operation-proof-v1` JSON statement for an accepted
plain room say. It never signs or submits a new call. It checks private operation
custody, workspace/subject/transport identity, the original request and native
intent, a freshly authored command against the retained native plan, and exact
reassembly of the retained signatures into the same call. A fresh lookup of that
call must confirm its native receipt before stable reply cell/sequence, recipient
and text are exposed. Feed entry numbers are not proof of a stable thread.

Public artifacts and the fresh native lookup are retained in a private sibling
proof directory and fsynced before success. The statement carries their hashes;
original attempt files are unchanged. Failed proof attempts preserve their evidence.
Opaque private-room payloads and non-say or multiple-target operations currently
refuse. A proof is evidence of a past accepted effect, not a live authority grant.

Qualification: three identity/transport/content/ref tamper tests pass. Actual
retained operation396 in the isolated hrl room reauthored/reassembled/looked up
without another write, returning its original acceptedCount115 receipt and
stable founder20 cell16132236063334032269/sequence1. Runtime suppression has its
own exact final/origin/content checks and preserves the original room resolution.
