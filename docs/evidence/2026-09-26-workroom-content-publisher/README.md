# Workroom content edit through the durable origin publisher

An accepted native Mini edit of content object `8001` by tool `7302` under
parent `7301` became a strict R source, a signed fn carrier, an accepted Mini A
tag-10 outbox record, and one protected fn POST. This used a **fresh** Mini A
catalog Store and fresh fn A/B Stores, separate from the earlier r5 publisher
and exchange fixtures. The workroom origin Store was copied read-only and its
historical edit-43 package was re-exported byte-identically before op16.

The qualified fn source is `bbf52159dcab19228bd6cd0b855b99dd6d68758d`;
the hbox `fn-host` image SHA-256 is
`432622d29a28d59455e01f3e5b426036c5862db21d5f7d1205a9304ab11e3505`
(core SHA-256 `6e569af117ba4afcf52bfd74f2a40ac222ead7701bb0b84bac799c53521bfe9e`).
The isolated fn operator profile set `max-article-octets=524288` and
`max-record-octets=18874368` **before** serving. The Mini Host was the linked
post-bbf image SHA-256
`919c3b7b64b7bff11d47a52993c7700b8028aa8596013cf396f41fd4f98c3038`;
the public Rust client SHA-256 was
`4e4beea360b5c0144b49ac6e4a08132e1ab7646d08a8a532bcc9091ba9c0b982`.
The private workroom origin config was distinct from the new A outbox seed
and storage root.

The origin package is 250,836 bytes, SHA-256
`14a69912b57efa8ed735a4a519b3c0872ef73cd9f53dcaae53ffc201bb0927ad`,
with accepted count 20. The strict R source is 343,679 bytes, SHA-256
`31e2b475949eb80846d56b96631ab73a05bebbda43ae39ab129a45f1fcbee250`.
The qualified fn `hybrid-sign-carrier` produced 351,204 bytes, SHA-256
`7aea225f40b37e2c77363604d72619c0ee6f7dfa71b5141e3ededa4c83d1d375`;
native `hybrid-verify-source` recovered the exact source and enrolled signer
tuple. That bounded verification result is retained privately; its full raw
log contains the hex source and is not copied here.

One public `mini origin-publish` invocation ran against that carrier and a
fresh Mini A catalog. Host op16 returned `proposed-fresh`. Ordinary signed Mini
submit installed tag-10 transaction
`43256431924785670667022619161948921173757276525858666129183502396848595423761`
at accepted count 3. Op18 exported a 703,805-byte frame (SHA-256
`a0aebfc2c3f53475ae9615edef30e95851784d26b74d51377dfb7e098cf62e20`)
whose exact carrier matched the retained signed bytes. Its Message-ID is
`<mini-grain-75066520320494335503287207186282537477487057135753415221093985984904776611415-19302899713478614648317033798292983451013749099175324834566009145612214627877@mini.invalid>`;
source identity is
`666e2f7375626a6563742f7631000101e06e8cd7b7eb4c9a50c2d96d8234ddfd7e936f443b36924c1f8ac06cf26aa988`,
package identity is
`23808894553684842308394564206727747287946157409933671891029673274204253173288`,
and origin-call identity is
`8785764972052745118910044703532207169440462768233617139172523875090433108882`.
The op18 origin and outbox receipts agree with the independently retained
origin package and signed Mini submit.

The publisher durably recorded fn POST attempt 1 before the network send.
The protected, certificate-pinned endpoint returned exactly
`240 article received OK`; an accepted marker was retained, and no attempt 2
exists. A same-state public command rerun exited 0 immediately, preserved the
attempt/result/accepted-marker mtimes, and made no second POST. Read-only fn
GROUP reported A=1 and B=1. B's native signed HDR and poll projection accepted
the served article; the 695,814-byte B event contains the exact R source and
Message-ID. The served carrier has a 75-byte fn transit header before the
authored signed carrier. **Typed Mini B submit and cursor ACK are separate
follow-up evidence**, not established by this publisher record.

The bounded files here are `content-summary.json`,
`fn-group-after-publish.log`, and `same-state-no-repost.json`. Private source,
carrier, calls, credentials, exact op18 frame, and Stores remain under
`/tmp/mini-workroom-publisher-20260926/` and
`/tank/fn/scratch/mini-workroom-publisher-20260926-1/`; no private artifact is
committed. Retained private SHA-256 values for review:

| Artifact under `publish-state` | SHA-256 |
| --- | --- |
| `outbox-prepare/decision.json` | `dd19f622ee96cffd6160bbb0dbcd2a3ba0e34d1a1875610c59219d1d6cd8cf79` |
| `outbox-submit/call.bin` | `e34c00e05251e00c486e5a817aba286dea6e0d8cd73f91c8c94a205781a24576` |
| `outbox-submit/outcome.json` | `3a8e48e03104f4beaaa39df76f4b78e547817fcc496c4c7156c96e4b8ef55134` |
| `outbox-export.frame` | `a0aebfc2c3f53475ae9615edef30e95851784d26b74d51377dfb7e098cf62e20` |
| `fn-post-attempt-1.json` | `6c8bdb7babce8e911140c7234e72e7f459733af4119cc8930326d91b12bbdeab` |
| `fn-post-result-1.json` | `17ea7aa8b3b68ab7d527c038f8384bd7130bf5e3ea07b1dac76ec0faeed110cb` |
| `fn-post-accepted.json` | `fdfb6e15c4129bc8253d662b94ed3fb62ab843ead366fe7f2a4f3bf352b0c158` |
