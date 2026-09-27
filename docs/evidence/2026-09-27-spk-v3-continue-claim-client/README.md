# Guarded v3 continue and fresh claim callback consumer

The v3 BEGIN consumer now authors a distinct Mini continue request with a
verified Created index. It accepts only a source-inspected plan that echoes
that index, the signed launch descriptor and its continue command digest, and
the retained Created receipt and custody bytes. The claim plan must echo the
same witness. Physical command selection uses the one signature-verified SPK
parse and rejects a digest mismatch; it has no first-create fallback.

The v3 claim consumer stages one op26 submission after checking the exact
private attempt, parent active marker, original BEGIN, and descriptor. It
retains the callback frame and accepts only the strict committed-v3 tag and
its source inspection, comparing the full frame, original claim and BEGIN,
source volume ID, selected command, process identity and receipt. The claim
accepted count must be strictly later than BEGIN, and receipt image boundary
must equal the inspected post-image boundary. Op27 receipt lookup is never a
physical permit. A failed or uncertain op26 leaves the one-shot marker.

INSTALL and START remain guarded. The committed-v3 inspection route and
event25 completion are still being source-qualified. A successful create
must additionally complete a signed STOP transition from serving to stopped
before continue; the current code does not assert that transition. Physical
volume custody and the v2 signed completion report still need a source-owned
join. This component cut does not run a Mini Store, start an app, or claim a
complete lifecycle.

The isolated hbox Rust snapshot used a private target, two jobs, and a 4 GiB
scope. `continue-focused-r6.log` records 14/14 scoped nextest passes;
`continue-clippy-r6.log` records strict all-targets Clippy pass.
