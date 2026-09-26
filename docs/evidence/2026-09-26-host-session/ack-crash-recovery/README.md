# Retained ACK after crash before archive

This bounded 2026-09-26 reproduction copied one real completed B short-skip
worker attempt into a new owner-private `pending` slot. Its durable state was
`Acking` for Mini transaction
`31376362735101321367946008363192293032548832719539946914460221980702111712317`,
with the original complete op13 `reply.frame` and `ack.json` still present.
The source archive and fn Store were not modified. The new state lived at
`/tmp/mini-ack-crash-HYzKx8`; private calls and keys are not copied here.

Client binary SHA-256 was
`078d5158984365d2058a5e503061de938475921d2dbff9aa35d341eae544df28`.
The source Host image was `minidregg-host-a-claim3` SHA-256
`39fd1db2ab4e488b4aaf7d0a00cfba781c42c40bef5c2a1139d80769be7ad8ee`.
The retained ACK frame SHA-256 was
`e1261b95b973938d61823ac432878d7a60b5d2ca449c652c946183395646a362`.

Running `mini consumer-drain-once` with the original pinned host, config,
socket path, and custody key returned `consumer wake stopped: ShortPage`.
The copied `pending` slot disappeared and the exact attempt appeared under
`completed/<transaction>`. `diff -qr` found no byte differences between the
source archive and recovered archive. This exercises restart after an exact
ACK reply was retained but before archive. It does not simulate loss of the
reply frame or a real process crash; the separate fresh equal-current native
skip probe established that one exact op13 repeat is a no-op at fn's current
cursor.
