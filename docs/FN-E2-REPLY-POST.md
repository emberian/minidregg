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

1. **Prepared:** Mini installs an absent-only unsigned plan containing the
   exact source, Message-ID, Q and parent/source/key bindings. If installation
   is uncertain, it reopens that slot. Equal bytes are idempotent; any
   different record or malformed record refuses and preserves the conflict.
   No signer call occurs before this plan is confirmed durable.
2. **Signed:** Mini first reads the signed slot. If absent, it asks fn's native
   signer to sign the prepared exact source under the selected keys, checks
   the result against the plan and full public keyset, then installs the
   exact source, signatures and rendered carrier into a second absent-only
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
uses fn lookup and never creates a new Message-ID. The first native fixture
must exercise these cuts and compare the exact source, signatures, carrier,
Message-ID and source identity across retry and owner reopen.

The local fn `hybrid-sign`/`hybrid-author` path and full-keyset verifier remain
cryptographic and I/O trust boundaries. SQLite's CAS, fsync and recovery are
physical assumptions. Mini's Lean codec/decision owns all record validation;
Rust transports opaque bytes. Fn's ACL2 core owns article identity, Store
admission and lookup verdict. Neither Python nor shell decides whether a
different record represents the same publication.

The live poll-to-ACK result is recorded in [FN-E2-LIVE-2026-09-24.md](FN-E2-LIVE-2026-09-24.md).
That run durably retained Q but did not execute this publication protocol.
