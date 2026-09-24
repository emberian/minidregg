# B3: durable fn reply publication from Mini Q

Status: implementation contract for the bounded local E2 experiment. It adds
no authority to the fetched fn report and selects no new governance profile.
The accepted Mini operation in `Kernel/FnConsumerOperation.lean` is the source
of the immutable application reply Q. Its original signed event also retains
the Store poll object, source identity and Message-ID of R. A current page
view, command stdout or fn consumer ACK is not an outbox authority.

## Publication identity and bytes

The publication key is Mini's durable deployment domain and semantics,
accepted operation transaction ID and original accepted event ID, the exact
Q codec bytes, R source identity and Message-ID, and an independently selected
fn signer profile and full public keyset. Mini re-admits the accepted event
before deriving a publication. It constructs one bounded RFC 5536 article
source in Lean from those fields under a fixed local `fn.test` experiment
policy. A domain-separated digest of the exact typed fields selects a stable
Message-ID. The source includes a correlation to R and a canonical encoding
of Q. No wall clock, arrival order, mutable content page, fn local article
number or fresh retry nonce selects either byte string.

The outbox has two opaque SQLite CAS slots per publication key, with exact
typed Mini codecs defining their contents. The physical path is a locator,
not the authority: every opened record is checked against the re-admitted
Mini operation and separately selected signer/keyset.

The first implemented construction packet is
`Kernel/FnReplyPublication.lean`. Its `Selection` carries the exact Mini
accepted event and signer keyset; it rejects a source/parent mismatch,
nonprinting parent Message-ID, wrong key widths and an oversized Q. A framed
cSHAKE preimage under the reply-profile v2 domain selects the reply Message-ID,
and Lean builds the exact source
for the live Q under a fixed local `fn.test` experiment profile. That profile
now includes a fixed, signed Date, because fn's portable author path requires
Date in the source. It is a synthetic fixture choice, not a general
publication clock: a production profile must select Date once at plan creation
and persist that selection, plus an explicit source-profile version, in the
prepared record and Message-ID preimage. The v2 domain bump here separates
this synthetic Date repair from the retained v1 refusal; it is not a general
profile migration protocol. The reply body is
lowercase hexadecimal of the exact canonical Q bytes. The probe on the live
254-byte Q checked byte-identical repeat, a different Mini event selecting a
different Message-ID, and CRLF parent-header injection refusal. Its framed
`Prepared` codec stores the exact source and Message-ID alongside the full
selection; re-admission checks both derived equalities and the 8,192-byte
record bound. The probe also rejected altered staged source and Message-ID.
This construction alone does not install the plan, sign, post or settle a fn
result.

`consumer-stage-reply-plan` now reopens the original Mini event, requires its
observed fn poll and Q, checks the independently selected reply signer pin,
then calls the existing opaque Rust SQLite `publish` for a selected sidecar
root. It always reads the stored bytes back and decodes and validates the
Lean `Prepared` record before reporting `durable-accepted`; an unreadable or
malformed readback is `uncertain`, and a valid different record is `conflict`.
The 2026-09-24 local trial used the accepted Mini transaction from the live
poll run. Before the Date repair it installed a 3,391-byte plan, exported an
816-byte exact reply source, recovered the same plan on an equal retry, and
returned exit 2 for a different Ed25519 public-key pin without exporting a
source. The candidate and readback SHA-256 were both
`38c99d542952297d84880584fbc60e66a68aca0c3de022a5790f29e546286521`.
An occupied sidecar containing malformed bytes returned exit 3 (`uncertain`)
and exported no source; it did not overwrite those bytes.
The non-secret trial files and SQLite byte images are preserved at
`/tank/fn/gates/mini-live-join-1d26-20260924/build/mini-evidence/b3-plan/`.
This sidecar is a separate physical SQLite root; its durability relies on
the same Rust/SQLite/OS assumptions as Mini's main image. No signer or fn
post was invoked in this trial.

The next typed packet adds `Signed`, a canonical record containing that
prepared plan and exact detached 64-byte Ed25519 and 3,309-byte ML-DSA-65
signatures plus fn's 48-byte source identity. Its Lean validation binds the original plan and signature widths
under a 12,288-byte bound; the live-Q probe checked a codec round trip and
short-signature refusals. Cryptographic verification and sidecar installation
of this record use fn's native `hybrid-sign-carrier`,
`hybrid-verify-source` and `hybrid-sign` commands. The host checks the full
public keyset and exact source from that native verifier, then installs the
detached tuple by absent-only opaque SQLite CAS and reads it back before
exporting signatures for `hybrid-author`. An already installed signed slot
is read first; retries reuse its exact bytes without calling the signer.
This host path built and completed an isolated native sign/post/cold-reopen
witness against the previously qualified fn e160 image, recorded in
[FN-E2-B3-NATIVE-2026-09-24.md](FN-E2-B3-NATIVE-2026-09-24.md). The later
combined topic/index image remains unqualified. The rendered carrier used
for keyset/source preflight and the detached signatures are separate signer
outputs. The preflight carrier is transient: the confirmed signed slot retains
the exact source, Message-ID, source identity and detached signatures that
`hybrid-author` consumes. Fn's author command verifies those signatures and
renders the admitted carrier under its own injection observation. The reopened
native carrier must be independently verified against the stored source,
identity and full keyset; its Path and Injection-Date projection may differ
from the preflight carrier. This packet does not claim a cryptographic proof.
The first native refusal probe pointed it at an absent prepared sidecar and
nonexistent private-key paths: it returned exit 2 (`unprepared`) before
creating a source or signed slot, so no signer call was reachable.
The first native sign/post fixture later installed a prepared plan, then fn's
`hybrid-sign-carrier` refused its Date-less source under
`fn-hc-required-sourcep`. It created no signed slot or post. The corrected
synthetic source adds the fixed Date before a fresh plan is staged and bumps
the Message-ID domain from v1 to v2, so the changed source cannot reuse the
old prepared identity. The old SQLite slot is retained as refusal evidence.
The first Mini host surfaced that definite fn refusal only as a generic exit 1.
The repaired sign stage maps native exit 1 to structured `refused`/exit 2,
native exit 3 to `uncertain`/exit 3 and other nonzero native exits to
`transport-fault`/exit 4 before any signed record or post is exported.
Unexpected spawn, output-read and parse exceptions still need a separate
boundary audit.

1. **Prepared:** Mini installs an absent-only unsigned plan containing the
   exact source, Message-ID, Q and parent/source/key bindings. If installation
   is uncertain, it reopens that slot. Equal bytes are idempotent; any
   different record or malformed record refuses and preserves the conflict.
   No signer call occurs before this plan is confirmed durable.
2. **Signed:** Mini first reads the signed slot. If absent, it asks fn's native
   signer to sign the prepared exact source under the selected keys, checks
   the result against the plan and full public keyset, then installs the
   exact source, source identity and detached signatures into a second absent-only
   slot. A lost CAS reply is resolved by reopening that slot. A retry uses
   its existing bytes and does not sign again. A conflicting signed slot
   refuses; a second concurrent candidate never replaces the first.
3. **Post:** Only the confirmed signed slot can feed the native
   `hybrid-author` command. Accepted, refused and uncertain remain distinct.
   An uncertain reply triggers a read-only lookup by the stable Message-ID
   and comparison with the exact authored source identity and source bytes,
   including the historical authorship verdict. Exact presence settles
   acceptance; a conflicting same-Message-ID article is retained as conflict
   evidence and refuses retry. Definitive absence permits retry of the same
   signed source and signatures. A transport fault without authoritative
   absence remains uncertain. An accepted fn result is not a Mini application
   result or a retention release.

The original Mini operation may commit before either sidecar slot exists.
Recovery reopens that Q and resumes from the absent stage; fn's consumer ACK
does not gate outbox delivery. Death after a prepared plan but before signing
resumes that exact plan. Death after signing but before a clear CAS response
queries the signed slot before making another signature. Death during post
uses fn lookup and never creates a new Message-ID. The isolated native fixture
exercised separate-process replay of the durable signed slot with unavailable
private keys, compared its exact source, detached signatures, Message-ID and
source identity, and verified the cold reopened carrier through fn's native
verifier against the persisted source, identity and keyset. It did not exercise
a lost post reply, uncertain-post lookup or process-death cut; those remain
required for a complete B3 recovery claim.

The local fn `hybrid-sign`/`hybrid-author` path and full-keyset verifier remain
cryptographic and I/O trust boundaries. SQLite's CAS, fsync and recovery are
physical assumptions. Mini's Lean codec/decision owns all record validation;
Rust transports opaque bytes. Fn's ACL2 core owns article identity, Store
admission and lookup verdict. Neither Python nor shell decides whether a
different record represents the same publication.

The live poll-to-ACK result is recorded in [FN-E2-LIVE-2026-09-24.md](FN-E2-LIVE-2026-09-24.md).
That run durably retained Q but did not execute this publication protocol.
