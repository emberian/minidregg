# Source map for the site

Every factual sentence on the hand-written pages, and the file and lines at main
(`5df8bb07`, 2026-10-04) it comes from. `status.html` is not listed: `gen-status.py`
generates it from the README's Honest state section (`README.md:61-87`), and the `website`
gate fails when it is stale. When a source changes, fix the page and this map in the same
commit. Paths are relative to the repository root. FRIENDS = `deploy/shell/FRIENDS.md`;
OB = `docs/OBJECTIVE-BEND.md`.

## index.html

| Claim | Source |
| --- | --- |
| a programmable shared world for people and agents | README.md:3 |
| every change is a signed request a Lean kernel admits or refuses | FRIENDS:74-75 |
| documents, applications, communities, computations share one set of rules; bounded delegation without unrestricted access | README.md:5-9 |
| devnet; re-genesis on a data-model or kernel-wire change; everything made is lost | FRIENDS:41-44 |
| no admission uses a proof | README.md:179-180 |
| private rooms main only; privacy not audited | FRIENDS:31, 377 |
| no native Host has admitted an Objective Bend program | OB:298-299; README.md:74 |
| public node: shell, documents, boards; no outside member enrolled | README.md:69; FRIENDS:37 |
| Lean owns semantics, Rust the physical boundary; capabilities, laws, read roots, funding; Rust decides nothing semantic | README.md:17-21 |
| re-execution at admission and on every replay | README.md:179-180; docs/SDK.md:110 |
| a correct calculation cannot grant itself permission; a reference is not ownership | README.md:21-23 |
| a law is checked on every change; a lock stops owner and operator | FRIENDS:177-186 |
| repository and host binary keep the name minidregg | README.md:147 |

## language.html

| Claim | Source |
| --- | --- |
| lazy open recursion over first-class, partial, composable specifications, after Faré | OB:3-6 |
| Mini supplies identity, authority, effect admission, funding, disclosure | OB:6-8 |
| specification `C → V → W`; final self; inherited super | OB:20-24 |
| `mix` formula; `fix` computes the fixpoint | OB:30, 33, 53 |
| call-by-name reference semantics, call-by-need machine | OB:51 |
| `{good = 7, bad = self.bad}.good` is 7 | OB:35-37 |
| `perform` yields a typed Plan, resumed with a typed response | OB:64 |
| the checker returns a typing derivation; affine and linear are at most once | OB:67-68, 73-75 |
| example (an excerpt) | docs/tutorial/ch4-specs.obend:10-20 (checked by the `website` gate) |
| `Billing` sees a later layer; `bill(2)` is 7, then 9 with `Surcharge` | docs/OBJECTIVE-BEND-TUTORIAL.md:590-609 |
| a gate re-runs every tutorial command and fails on a changed output | scripts/check-objective-frontend.sh:23-24; scripts/check-objective-tutorial.ts:45-48 |
| proofs in `Theory/ObjectiveBend*.lean`; axioms `propext`, `Classical.choice`, `Quot.sound`; no `sorry` | OB:172-174 |
| soundness (weak head) | OB:181-182 |
| preservation | OB:184 |
| no refusal; divergence and exhausted limits remain possible | OB:185 |
| completeness at large enough limits; no bound on them | OB:189, 199-202 |
| every compiled call runs the fast machine, equal by theorem | docs/OBJECTIVE-BEND-BACKENDS.md:17 |
| the default build re-checks none of the proofs | OB:227-233 |
| no source-to-Core4 theorem; the TypeScript front end is trusted | OB:214-215, 309-312 |
| no native Host has admitted an Objective Bend program | OB:298-299 |
| no kernel delivers a response to an activity | docs/OBJECTIVE-BEND-EVENTS.md:12-13 |

## architecture.html

| Claim | Source |
| --- | --- |
| a signed request; admitted with a receipt or refused with a reason | FRIENDS:74-77 |
| checked against capabilities, laws, exact read roots, funding | README.md:17-20 |
| a computation re-run at admission and on every replay; no admission uses a proof | README.md:179-180; docs/SDK.md:110-111 |
| Selvage outside the deployed umbrella except 12 modules through the digest backend | Deployed.lean:6-9, 14-16 |
| grants with verbs; revocation | FRIENDS:161-166, 221-222 |
| a law is checked on every change; a law that denies everything is permanent | FRIENDS:177-186 |
| the lock transcript (comments moved to their own lines; the unlock refusal's detail elided) | FRIENDS:181-184 |
| receipt: transaction id, world root, confirmation `installed` / `replayed` / … | docs/SDK.md:18-20 |
| fourteen refusal reasons | Compiler/RefusalReason.lean:58-88; FRIENDS:563-580 |
| a lost reply is a lookup of the same call bytes | docs/SDK.md:77-78 |
| a retry returns the same receipt | FRIENDS:173-175 |
| SDK in Rust and TypeScript, byte-identical | docs/SDK.md:3-5, 88-89 |
| on the device; operator untrusted; member-selected Lean consent process re-derives and returns the header bytes; nothing else is signed | docs/SDK.md:39-46 |
| a browser has no consent process and must not sign until a bridge exists | docs/SDK.md:89-93 |
| private rooms: main only, devnet quality, privacy not audited | FRIENDS:377 |
| sealed on the member's machine; key held only wrapped to each member | FRIENDS:380-381 |
| X25519 + ML-KEM-768 wrap | FRIENDS:411-413 |
| the node sees membership, timing, sizes in 64-byte steps | FRIENDS:408-409 |
| founder key trust on first use | FRIENDS:403-405 |
| Generic Simplex BFT engine in Lean, compiled native | README.md:53-55 |
| n = 3f + 1, at most f Byzantine | docs/GENERIC-SIMPLEX-NATIVE.md:11-12 |
| safety over the engine model; liveness not established; four replicas on one host | README.md:78 |

## join.html

| Claim | Source |
| --- | --- |
| accounts by hand; FRIENDS.md is the guide | FRIENDS:1-9, 79-87 |
| make an ssh key; send the public half and a session name; `mini>` prompt | FRIENDS:81-86 |
| works on the node; journey J0–J8 | FRIENDS:13-22; README.md:69 |
| not on the node: rooms, chat, private rooms, key rotation, proxy mode, librarian, paying to enrol | FRIENDS:23-35 |
| re-genesis keeps ssh and signing keys and erases what you made | FRIENDS:41-44 |
| hosted key on the box, readable by the operator and other members' sessions; keep nothing precious | FRIENDS:46-52 |
| README, AGENTS.md, developer guide; no users; a format change is a rebuild; old shapes refuse; say what breaks | README.md:107; README.md:189-191 |
