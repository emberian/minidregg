# Human event22 tickets and private entrance preparation

`issue-human-ticket.sh` stages Alice Web, Bob Web, and Alice API as separate
event22 tickets. It checks retained accepted app/session receipts and the
qualified signed-SPK package and schema bytes. It selects the matching web or
API interface and an explicit non-obsolete signed role with the exact
operator-reviewed permission list. Host authors/previews the request, while
Mini op56/57 replans and assembles it against the current image. Op54 is
one-shot; op55 performs exact receipt-only recovery.

`prepare-human-entrance.sh` runs op55 against an exact retained ticket,
compares the four-field receipt, re-inspects the source plan and reauthors the
same request. It rejoins the full ticket package/interface/schema scope and
ceiling role to the original signed-SPK inspection, selected role and operator
policy. It derives the issue index from acceptedCount and joins the
human session, subject, kind and ticket to the fixed allocation. The native
`human-custodian-init` CLI creates private tokens and `custodian.json`; the
script adds explicitly pinned dispatch signers and atomically renames the
completed owner-private entrance into place. SPK still checks every signer
against the current op36 source plan before any dispatch.
Interrupted read-only ticket probes remain untouched; a later preparation
uses the next numbered private probe. An interrupted native custody staging
directory remains blocked for explicit audit, rather than recreating tokens.

`sh -n` and ShellCheck passed for both scripts. Isolated Linux schema fixtures
in `/home/hbox/mini-agent-ticket-schema-r1` exercised Alice's full ticket
prepare/approve/seal/one-submit/repeat-lookup, Bob and Alice API source
interface selection, route rendering, and refusals for altered event22
receipt, crossing Alice's ticket into Bob's entrance, and changing the
interface root while preserving the coarse ticket IDs. The fixture uses
fake Host/Mini/SPK commands only for shell transport and retention checks;
it does **not** establish native admission or authorize live r3 Store use.
The native custodian CLI registration and accepted r3 sessions must qualify
before these scripts can prepare a production entrance.

`native-cli-and-probe.log` additionally used the actual isolated hbox Rust
`human-custodian-init` binary with fake Mini/Host transport. It verified
private token files, atomic route installation and a second numbered probe
after a retained interrupted first probe. That binary is a component build,
not a source-certified deployment artifact.
