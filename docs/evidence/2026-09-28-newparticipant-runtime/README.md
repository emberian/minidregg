# Fresh participant runtime attempt — 2026-09-28

This record covers one fresh, private Persvati Store. Bootstrap, signed sponsor
factory read, independent participant enrollment, and receipt-only historical
lookup passed. The participant received a signing key, not an account or
resource grant; this is not a complete Gate A application journey. No
pre-existing Store, genesis image, or key is reused for the initial fixture.
The newcomer subject and key IDs are allocated by the shared client
namespace during `mini enroll --action plan`; the fresh genesis has only the
sponsor subject 7.

The reproducible launcher is
[`newparticipant-acceptance.sh`](../../../native/resource-client/newparticipant-acceptance.sh),
SHA-256 `37f744d958150af153f67c96018015121b5220168be3a55a79e2aca2b049f07f`.
It uses Mini's typed bootstrap, persistent public socket, participant workspace
init/import, and signed factory read. It leaves the prospective newcomer
unadmitted for the separate client plan/seal/submit sequence. The private run
root is reserved as
`/home/ember/build/minidregg-newparticipant-e22d16b-r3-run1` on `persvati`;
it was absent before launch. The launcher completed in 19.55 seconds, producing
its typed pinned config, persistent public socket, sponsor workspace, and
signed factory read under that root. Its `handoff.json` was returned. The
private Store has no accepted transaction at this handoff.

Qualified supporting Linux executables:

| Executable | SHA-256 |
| --- | --- |
| Host from source cutoff `e22d16b` | `723940446d3e0256bd446b07ca8d67ea9d67295d8c7cc78e08bb2487ffbe3db2` |
| Mini from source cutoff `0007925` | `3e9cb1ca488995a0a591ea6db8f9b4b6b59d9629782daf6babb294620c74513d` |
| SQLite Store helper | `ad03aede839259c1884383fc97f141a3fe106ba2f2cbae0df6f7916676fe193f` |
| Ed25519 verifier helper | `c84004123ae6f02654cb6749e4105e351199618aaefce5755a2a0bb10bd0892b` |

The Host's source/artifact readback and all 363 Lean modules passed; its
private build manifest SHA-256 is
`862e17fcf0a462bdad6b830cd3a46e13801af1a2339a1ee9e41f1ef552d24afb`.
The qualified Mini's full source archive and build manifest hashes are retained
in the private build manifest.

The same public socket accepted `mini enroll --action plan`, `seal`, and
`submit` with exit code zero. Shared namespace allocation chose subject
`9594942322447678104` and key ID `10489544371237092821`; neither appears in
the one-sponsor genesis. The source Host installed accepted record 1. Its
transaction ID is
`49905845347260400886717426455403128851554073879650940306252509606507530227960`;
event ID is
`49453875511552072654583563393425856536846496381386780171946997682782979141723`.
The result has type `minidregg-participant-enrollment-result-v1` and authority
`admitted-key-only`. Its SHA-256 is
`22dd0f1933cfa9ff6a3ae406c8e8c85a27d369d7a954a441a5cb273ece4cebc7`.
Exact receipt-only `mini enroll --action lookup` returned the same receipt and
left that result hash unchanged; no second mutable submit occurred.

| Step | Elapsed seconds | Result |
| --- | ---: | --- |
| Fresh fixture bootstrap, service, signed factory read | 19.55 | pass |
| Enrollment plan | 2.427 | pass |
| Detached sponsor and new-key signatures, assembly | 0.546 | pass |
| Signed submission | 0.807 | accepted record 1 |
| Historical lookup | 0.644 | same receipt |

The retained private command, plan and ingress SHA-256 hashes are respectively
`229fae7ade11b278fbeaeae3049b46bf0ae402b69da977fd8dfaa7d365241673`,
`00e05138b42257c4fe12905f7412c842b45961c5fd9bec8eca9f2e51f80d0d75`,
and `7a4c07a91a5a1fa12f70f0cc1913762dc5dacabac5253189e4bc682e05fa80d1`.
Private per-step stdout, stderr, timing, pinned config, and full receipt remain
under the fixture root. This file contains no private key, raw signature,
Store, or signed ingress.

After enrollment, the sponsor used the same Store to create one declared
resource through current birth authoring (accepted record 2), delegated a
scoped child capability to the newly allocated subject (record 3), and the
newcomer used its own signing key to read and invoke that resource (record 4).
The [workspace journey](workspace-journey.md) records exact retained paths,
full artifact hashes, and the source-authored operation receipts.
The source-created resource ID is `17159261934168749150`, its sponsor owner
capability is `9822429982843237991`, and the delegated child capability is
`15762484371575563069`. The newcomer’s signed readback found field 2 equal
to 1, with resource root
`52508571685590115096069643834569660389787472896661508995892086544134842230801`.
The retained transaction IDs for birth, delegation and invocation are,
respectively:

| Accepted count | Operation | Transaction ID |
| ---: | --- | --- |
| 2 | Sponsor resource birth | `56293972426066610661573798462120266857968446640864720411551360738844299759139` |
| 3 | Scoped delegation to newcomer | `56254409449888250226808378939622334164181992153944127387565619452830244340819` |
| 4 | Newcomer signed invocation | `66806890370008592955042648984267456502690309751928710946430056815131340828080` |

The phase-2 commands took approximately 4.2 seconds for birth, 4.1 seconds
for delegation proposal and 3.4 seconds for submission, then 2.1 seconds for
newcomer read, 2.0 seconds for invocation proposal, 2.9 seconds for submission,
and 1.2 seconds for signed readback (each includes SSH). The delegation's
receipt-only historical replay took 1.3 seconds. These are the original
resource lane timings, not a throughput benchmark.

The public socket was then stopped at verified old server PID `92431` and
restarted with the same pinned Host and Mini at PID `135440`. On cold reopen,
the enrollment receipt-only lookup returned the same result hash above; the
newcomer’s signed resource read again returned field 2 equal to 1. Those
checks took 0.317 and 0.713 seconds respectively. Private logs are retained
under `enrollment/cold-*` in the fixture root. This cold check exercised the
same Store, not an exported or copied image.

The sponsor subsequently installed a deny-all rule on the shared resource as
accepted record 5. A fresh newcomer signed read and the sponsor's attempted
policy-repair proposal both stopped at the current-law observation query;
the newcomer's previously accepted call still returned its exact historical
receipt. The [workspace journey](workspace-journey.md) pins the law-change
receipt and refusal artifacts. This is an observation-surface lockout, not a
separate rejected management submission or a denial of the enrollment itself.

This proves runtime identity enrollment followed by an ordinary delegated
resource action for a second signing subject. The newcomer did not receive
its own account or factory/payer authority, so independent newcomer resource
birth remains unqualified. This run does not demonstrate a second human and
Hermes in one application grain, shared application hosting, or fn publication.
