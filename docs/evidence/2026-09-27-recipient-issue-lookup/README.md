# Recipient-only application share issue lookup

Commit `3761f74` adds `mini share-issue-receipt-lookup`. A second controller
supplies one exact source-authored `ingress.bin`, its own fixed Mini Host/config
and public socket, four expected historical receipt fields, and a new private
output directory. The client sends **only native op29** with those ingress
bytes. It retains the request marker, exact ingress, reply frame, binary
outcome and typed Host inspection. The returned receipt must be replayed and
match transaction ID, event ID, accepted count and image boundary exactly.
Host/config/ingress are checked again after the lookup and after inspection.

The Host outcome inspection is a direct local call to the pinned executable;
no op8 request is sent over the public socket. The recipient does not receive
the issuer's approval, signing plan, custody key, original submit marker or
history directory. This is a read-only historical fact, not a new share issue
or a current-use authorization.

Source identities: `native/resource-client/src/main.rs` SHA-256
`ff10fcbe8eb5c649b0b798d503c58d608db6aed7c4100aba30eb2b1b973436a2`;
`native/resource-client/src/share_issue_receipt.rs` SHA-256
`fe347bb22114fd6e35ce3cad1d81a867418fe2ab13b1e21ed539f955982b1d7b`.

Validation used a private exact-source copy at
`/tmp/mini-share-issue-receipt-check` with an isolated Cargo target. The
[focused nextest log](nextest.log) records 3/3 PASS, including a loopback Unix
transport capture that checks the pinned envelope carries op29 and the exact
ingress bytes (SHA-256 `958ff9adf4052cda36896cb3affef38c8a9207f62d29d5e9539be4c5500bb11e`).
[Strict all-targets Clippy](clippy.log) passed (SHA-256
`4f27ac380b22e1d975eee20ce727fa8cbc09061177f6253af0777fd4de7b7506`).
`cargo fmt --check` passed; its captured log is empty.

No live share issue, cross-controller application opening, or native installed
app acceptance was executed for this client cut.
