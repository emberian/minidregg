# Retained r3 first workroom birth

This is the first accepted birth in the **existing** signed-GitWeb r3 Store on
hbox. The protected fixture is
`/var/lib/minidregg/spk/fixtures/gitweb-v2-20260927-client-session-r3`;
the append-only action is `continuations/first-birth-retry-0002` beneath it.
The original `base/workroom/birth-attempt` call, config, manifest, and absent
`retry-0001` are unchanged. No workroom or application continuation ran.

The original 212,637-byte call has SHA-256 `1ff9d4ad41644a376884d13a6092787a2ca6a2a7d99c30659263f04221d8bdb7`;
the retained config has SHA-256 `c2c79aa69f66ecc7922f69f620a9dd9ca24cfea25cd94282fcb1a40c2b8296b8`.
The original attempt still identifies Host2649 SHA-256
`95cd66117983796e4887f03f3ddd25b048d70713fb56ae93c36dbbc379139285`.
The separately selected, source-qualified finite-case repair Host has SHA-256
`2c28356f8c59dc5ec4d17c594ed718bca3f73f336790c8eb30bb395557f28bf7`.
`transition-intent.json` was fsynced before the fresh lookup or submit. Its
selected ELF copy is under the protected action, not in this portable record.

The original Store's physical `forward-link.sqlite3` SHA-256 was
`8ce7e8e82cfd7b750bbfdebff10e477479212d253e2e02ae11f5117a183b4b29`,
the recorded genesis physical hash. A fresh, separately retained exact-call
lookup returned typed `absent` and did not change that hash. The original
source manifests and binary pins passed before the one direct submit.

The direct submit ran once under a 900-second deadline in the hbox **user**
systemd manager, unit
`mini-spk-platform-r3-birth-successor-submit-client-session.service`,
invocation `9043673f6b2149b5aa0e2a3eea94fbba`. It exited 0 in 5:44.57 wall
seconds and returned `confirmed/installed`, accepted count `1`; the exact
132-byte native response has SHA-256
`21672e21e1caa002ad76e906542de4b5c77eabd73e6587180c046eb823d31c88`.
The physical Store changed to SHA-256
`e5515e158fdfb03afdafc3951a3a73c2b779bac37eb8428a146c8244611e30e5`.

A separate read-only cold lookup ran in the hbox **user** manager, unit
`mini-spk-platform-r3-birth-receipt-lookup-client-session.service`, invocation
`a28384bb6b0746298bbfa9b2a4bae623`. It exited 0 in 1:50.53 wall seconds,
returned `confirmed/replayed`, and left the Store at the same physical hash.
The four receipt fields matched exactly: transaction
`21452126580387832849295759345841801346003355297904064439953413667585429370297`,
event `42274396663273669929974823207448344706044618477292890883734173696896699073815`,
accepted count `1`, and image boundary
`14446137707838494980671458133208750893239572581456245670174131992965079679473`.
`final-verdict.json` and `receipt-sha256.txt` preserve the keyless result and
native artifact hashes; the latter passed a full check on hbox. The portable
files here match their protected originals byte-for-byte.

The existing `resume-base.sh` expects receipts at
`base/workroom/birth-attempt/retry-????.json`. This action's real results are
instead `continuations/first-birth-retry-0002/submit.json` and
`lookup-after-submit.json`. They must be append-only adopted with an explicit
provenance mapping, or the driver narrowly updated for these exact action
paths, before any later base continuation. Do not fabricate or overwrite the
original `outcome.json`. The accepted birth alone is not INSTALL, START,
browser, agent API, or same-app content acceptance.

This directory contains only typed projections, timings, hashes, and keyless
intent/verdict metadata. It excludes signed call/config bytes, keys, binaries,
and the Store.
