# Fresh participant runtime attempt — 2026-09-28

This record covers one fresh, private Persvati Store. Bootstrap, signed sponsor
factory read, independent participant enrollment, and receipt-only historical
lookup passed. The participant received a signing key, not an account or
resource grant; this is not a complete Gate A application journey. No
pre-existing Store, genesis image, participant ID, or key is reused for the
initial fixture. New subject and key IDs are allocated by the shared client
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
