# Selected exchange between two independently credentialed Stores, 2026-09-30

One run of
[`selected-exchange-journey.sh`](../../../native/resource-client/selected-exchange-journey.sh)
from commit `c0e933a`, on hbox, under the private root
`/tank/dregg-preview/m9-second-node-20260930/run5` (mode 0700). It passed end to
end. `public-summary.json`, `timings.tsv` and `input-sha256.txt` in this directory
were copied from that root. The inputs' hashes were identical at the start and
the end of the run. This file contains no key, signature, Store or ingress.

## Topology

| Party | Identity | Credential |
| --- | --- | --- |
| Store A (source) | domain 8611, sponsor subject 7 | its own sponsor key, public `32c35063…4807bb`; genesis enrolls only this key |
| Store B (recipient) | domain 8612, sponsor subject 8 | its own sponsor key, public `af1aa3f5…276dc9`; genesis enrolls only this key |
| fn node | fresh Store and node, loopback TLS NNTP on port 11241, local control socket | fn source `6462bd687eb68cdbdf4f57528e2e6f0dacd4d5a4` |

All three ran on one host. The Mini client's fn POST target is loopback-only, and
the Host's fn poll uses fn's local control socket, so the recipient Host, the
publisher and the fn node share a machine. Separate machines are item 13.

The fn image is the fn lanes' published build at
`/tank/fn/images/6462bd687…` (launcher `0579596923a9…`, core `e3ca1ee27181…`).
It was used read-only. fn `7aad444ce` records "manifest certify … run-ec68
--all at 6462bd687, 135/0". The fn Store, TLS certificate, posting principal and
consumer registration were all created fresh in this run.

| Binary | SHA-256 |
| --- | --- |
| Host (`e22d16b-r3`; closure unchanged to `c0e933a`) | `723940446d3e0256bd446b07ca8d67ea9d67295d8c7cc78e08bb2487ffbe3db2` |
| `mini`, built from `c0e933a` with `nightly-2026-06-21` | `7d1f049dee52a61b916804230fa851d6ccab485b2ba659c8542ce25ea574acc5` |
| SQLite Store helper, pinned toolchain | `599bc4e6c1a04ab42e4ec4c18f4d47423e9df903006bba1ac2c2b880ff29fbfd` |
| Ed25519 verifier helper, pinned toolchain | `71b8d73424920d18aa26f76b8594cc802de640da38c58ef79e3cc9ae1940b753` |
| journey script / `newparticipant-acceptance.sh` | `abe38ba8…0cd` / `a49f7b5f…b19` |

## How B learns A's identity without A's secret

The release names `ownerSubject` 7, a subject number local to each Store. B
checks the owner signature against *B's own* current key for subject 7, requires
the recipient capability to be held by subject 7, and requires the inbox law to
be exactly `eq request/subject 7`. So B enrolled A's **public** key at A's home
subject:

1. B planned the enrollment with `--new-public-key a/sponsor.pub --home-subject 7`.
2. A's process ran `mini enroll --action possess`. It read only B's retained Plan
   and command inspection, checked that they name A's key at subject 7, and signed
   the possession header (header SHA-256 `ea23d8da…`).
3. B sealed with that detached signature and submitted. B admitted accepted
   record 1 (tx `102363198217…5096`). The result has `keyPath: null` and
   `admitted-key-only`. No file in B's root names A's secret key path (checked).

B then created its inbox `10504888637012766587`. It delegated child capability
`14187484279792257386` (`observe,mutate`) to subject 7, and installed the exact
owner-subject law. Every one of those operations was signed by B's own key.

## What ran

| Step | Result |
| --- | --- |
| Source content | A's `notes` resource holds atom 7401 (selected text) and atom 7402 (unselected text). A's signed read shows both. |
| `prepare`, `publish` (A's key; A's service stopped, direct Host) | Source event14 installed: tx `4225907109944016614461895683888208535178840199608575031471524834655718534969`, accepted 3. fn replied `240 article received OK`. One `fn-post-attempt` marker. |
| `receive-transport` (B served) | Authenticated local fn poll at position 3. fn's ACL2 `consumer-article` returned a 1,080-byte stored article that ends with the exact 855-byte authored article. The Host projected the exact 419-byte owner packet. B event13 installed: tx `10259611883041273727857910079077833078408496879473780068089509269879894538480`, event `81442599787838077706218083500482412302009989953889020490759042605612706536714`, accepted 5, image boundary `78376631292392673094295113533925064241887293043408016682996396659290837104978`. |
| Exact retry | A second `receive-transport` did exact op21 lookup and returned `replayed` with all four receipt fields byte-identical. It made no second event13 submit. A second `publish` left exactly one POST attempt marker. |
| `verify-transport` (corrected intent kind, end to end; B stopped, direct Host) | The fresh signed read of B's inbox found atom id = the event13 tx: live, inline object schema 11, payload equal to the packet. Observation SHA-256 `a9442003…982a`. |

Packet SHA-256 `083ae998b101f081a14d80127c7626fed60db97c15259b40a30630781f6ba99b`.
Article SHA-256 `9aa67d4a…c8cb`. fn stored article SHA-256 `2326c02b…12a0`.
fn `fn-r` report SHA-256 `d0daafc6…212f`.

## Disclosure (checked by inspection)

- The packet contains the selected text exactly once and the unselected text zero
  times.
- The article carries the packet base64-encoded, so a raw grep of the article
  would find neither text. The journey therefore decodes the body of **fn's
  stored article**. That body is byte-identical to the packet (SHA-256
  `083ae998…`), with the selected text once and the unselected text zero times.
- A's signed source view contains the unselected payload, so the absence check is
  not vacuous.

This checks one selected release. It does not establish absence of every
private-history disclosure.

## Refusals at their boundaries

| Case | Boundary | Result |
| --- | --- | --- |
| Tampered expected article (Subject header altered) | Host `selected-release-fn-legacy-poll` against the real fn Store | `fn stored article lacks exact selected owner source suffix`. No packet or ingress was written. Nothing was ACKed. |
| Tampered packet (one byte of the selected text changed after A signed a fresh release) | B event13 admission | `refused`, phase `admission` |
| B's own key signing a release that names subject 7 | B event13 admission | `refused`, phase `admission` |
| Fresh A-signed release wrapped for target root `1` | B event13 admission | `refused`, phase `admission` |
| B logical image before and after the three admission refusals | Store read-to | identical, SHA-256 `fc11c70f…c3a8` |
| **Positive control:** the untampered fresh release, through the same wrapper and the same current roots | B event13 admission | `installed`, accepted 6 |

B's admission refusal detail is always the generic `request refused`. The
positive control is what attributes each refusal to its one mutation (byte,
signer or root) rather than to the wrapper. The 09-28 wrong-root refusal was on a
different fixture; this one is on the exchanging recipient itself.

## Limits and findings

- **The release law locks B out of its own inbox.** Signed reads are
  policy-admitted. Under `eq request/subject 7`, B's sponsor (subject 8) read of
  the inbox was refused with the encoded `observation refused` outcome. The policy
  observation that re-lawing needs goes through the same admission. The 09-28
  deny-all lockout recorded that refusal; this run did not exercise it
  separately. So the `verify-transport` readback
  is signed by A's home identity at B, the only subject the law admits. B's
  credential authorized the genesis, the enrollment, the inbox, the delegation
  and the law, but it cannot read the result.
- **Owner identity is a bare subject number.** Cross-Store exchange only works if
  the recipient can take the owner's home subject, so the recipient's sponsor
  subject must differ (here 7 against 8). A recipient that already uses the
  owner's number cannot receive from that owner.
- This is transport only: no fn-e verdict, no event17 coverage, no fn cursor ACK.
  The consumer committed ACK stays 0.
- The run used one `mini selected-exchange` contract that names both A's key
  (owner) and A's home identity at B (readback). Each signature was still made
  only with its owner's key file.
- The timed steps sum to about 4.0 minutes on a shared, heavily loaded hbox
  (load average 30–40 when the session began); see `timings.tsv`. Earlier attempts under the same root: run1 and run2 stopped on
  journey-script bugs, run3 passed before the positive control existed, and run4
  passed from the pre-commit working tree.
- Every Mini and fn service the run started was stopped. No `mini serve` or fn
  `sbcl` process from this root remained afterwards (checked).
