# Source map for the site

Every factual sentence on the hand-written pages, and the file and lines it comes from, on
`lane/W14-WEBSITE-REGEN` over main `df0cd116` (2026-10-05). `status.html` is not listed:
`gen-status.py` generates it from the README's Honest state section (`README.md:61-89`), each
row carrying the landing commit or journey row it rests on, and the `website` gate fails when
it is stale. When a source changes, fix the page and this map in the same commit. Paths are
relative to the repository root. FRIENDS = `deploy/shell/FRIENDS.md`; OB =
`docs/OBJECTIVE-BEND.md`; EV = `docs/OBJECTIVE-BEND-EVENTS.md`. A commit id is a landing
commit on main; a journey row is a row of `scripts/pipeline/journey-rows:15`, run by the
continuous runner (its tables live outside this repository: `objective` PASS with 17 rows and
2 readbacks, `activity` and `seats` ABSENT, at main `4795b657`).

## index.html

| Claim | Source |
| --- | --- |
| a programmable shared world for people and agents | README.md:3 |
| every change is a signed request a Lean kernel admits or refuses | FRIENDS:81-84 |
| documents, applications, communities, computations share one set of rules; bounded delegation without unrestricted access | README.md:5-9 |
| devnet; re-genesis on a data-model or kernel-wire change; everything made is lost | FRIENDS:41-44 |
| no admission uses a proof | README.md:180-181; docs/SDK.md:136 |
| private rooms main only; privacy not audited | FRIENDS:31, 386-388 |
| a native Host admits Objective Bend programs on scratch worlds, by re-execution; none is deployed | OB:299-346; native/resource-client/objective-native-acceptance.py:88-134; journey row `objective`; commits 6df4602f, a2454432 |
| public node: shell, documents, boards; no outside member enrolled | README.md:69; FRIENDS:13-22, 37 |
| Lean owns semantics, Rust the physical boundary; capabilities, laws, read roots, funding; Rust decides nothing semantic | README.md:17-21 |
| re-execution at admission and on every replay | README.md:180-182; docs/SDK.md:135-136 |
| a correct calculation cannot grant itself permission; a reference is not ownership | README.md:22-23 |
| a law is checked on every change; a lock stops owner and operator | FRIENDS:186-196 |
| repository and host binary keep the name minidregg | README.md:113, 149 |

## language.html

| Claim | Source |
| --- | --- |
| lazy open recursion over first-class, partial, composable specifications, after Faré | OB:4-6 |
| Mini supplies identity, authority, effect admission, funding, disclosure | OB:6-9 |
| specification `C → V → W`; final self; inherited super | OB:22-25 |
| `mix` formula; `fix` computes the fixpoint | OB:32, 35, 54 |
| call-by-name reference semantics, call-by-need machine | OB:53 |
| `{good = 7, bad = self.bad}.good` is 7 | OB:38 |
| `perform` yields a typed Plan, resumed with a typed response | OB:66 |
| the kernel side of activities (checkpoint, answer slots, resume with view, paid exhaustion, abandonment) is compiled and proved; no Host operation reaches it | EV:15-19, 161-340; commits 8194e09d, 67362781, d1ce7b0c |
| the checker returns a typing derivation; affine and linear are at most once | OB:69-77 |
| example (an excerpt) | docs/tutorial/ch4-specs.obend:10-20 (checked by the `website` gate) |
| `Billing` sees a later layer; `bill(2)` is 7, then 9 with `Surcharge` | docs/OBJECTIVE-BEND-TUTORIAL.md:683-705 |
| a gate re-runs every tutorial command and fails on a changed output | scripts/check-objective-frontend.sh:27-28; scripts/check-objective-tutorial.ts:1-8, 40-48 |
| proofs in `Theory/ObjectiveBend*.lean`; axioms `propext`, `Classical.choice`, `Quot.sound`; no `sorry` | OB:179-187 |
| soundness (weak head) | OB:194 |
| preservation | OB:197 |
| no refusal; divergence and exhausted limits remain possible | OB:198 |
| completeness at large enough limits; no bound on them | OB:202, 212-218 |
| every compiled call runs the fast machine, equal by theorem | docs/OBJECTIVE-BEND-BACKENDS.md:17; OB:182-188 |
| when the checker accepts the front end's output it is typed, never refused, a finished run is a deep evaluation; the checker's reading of the packet is the elaborator's term | Compiler/ObjectiveBendFrontEndAdequacy.lean:34, 43, 51; Compiler/ObjectiveBendTermWire.lean:69, 280; OB:437-446 |
| the default build does not re-check the proofs; the `ObjectiveProofs` gate does, with a statement and axiom snapshot | OB:243-262; scripts/check-objective-proofs.sh:1-14; ObjectiveProofs.lean:1-4 |
| no surface semantics; the front end is one Lean program, trusted; the receiver re-runs it and admits only an equal core | OB:226, 437-466; Kernel/ObjectiveBendNativeAdmission.lean:378-400 |
| a native Host admits Objective programs on scratch worlds, not on the public node | OB:299-346; journey row `objective` |
| the kernel's activities, object records and seats have no native route | EV:15-19; OB:348-385; docs/SEATS.md:9-17 |

## laws.html

| Claim | Source |
| --- | --- |
| a law is a predicate checked on every change to a resource, whoever proposed it | OB:414-421 |
| three things called law: the cell law, the `.obend` spec `law` (never reaches admission), `requires` (recorded, not checked) | OB:414-435 |
| admission clauses `invariant`, `guard`, `permit`, `forbid` are a design, not built | OB:428-435; Compiler/ObjectiveBendParse.lean:640 |
| every law state begins with the slot `objective/artifact`; `-1` for a command without an Objective claim | Pred/Core.lean:156; Kernel/DeclaredResourceController.lean:214, 514; OB:387-401 |
| the `objectivePin` clause accepts only steps naming a pinned artifact; an ordinary command is refused | Pred/Core.lean:372-395; Kernel/DeclaredResourceController.lean:523, 534 |
| no turn installs the pin at object birth | OB:404-412; Kernel/ObjectiveActivity.lean:1993; Kernel/ObjectRecord.lean:185 |
| a cell is an object only with a record (pin, law, upgrade policy, payer); a birth without one, or of another package, is refused | Kernel/ObjectRecord.lean:62-70; Kernel/ObjectiveActivity.lean:2933, 2943 |
| every declared-state write is judged by the object's law over the old and new state; a refusal names the clause and commits nothing | Kernel/ObjectRecord.lean:202-209; Kernel/ObjectiveActivity.lean:2904, 2915, 2925; EV:357-385 |
| a resumed activity's write is judged as its birth subject, never the deliverer | Kernel/ObjectiveActivity.lean:2915-2921; EV:357-385 |
| an activity is a persisted checkpoint plus one await; one decider, one deadline, decided once | Kernel/ObjectiveActivity.lean:141-166; Kernel/AnswerSlot.lean:33-50, 125-136; EV:161-215 |
| a resume delivers the outcome and the state and version read in the same turn; no write is computed from a stale read | Kernel/ObjectiveActivity.lean:533, 2338, 2370, 2400; EV:218-250 |
| exhaustion is a paid turn; ended activities leave tombstones; abandonment after deadline plus grace returns the purse minus the timeout fee | Kernel/ObjectiveActivity.lean:1587-1612, 2647, 2769, 2842; EV:325-356 |
| one public tariff prices every declared envelope, for native admission and activities | Kernel/ObjectiveTariff.lean:17-52; Kernel/ObjectiveBendNativeAdmission.lean:468; EV:306-324 |
| a seat holds one side of a contract in its own Book account; law is offer safety; judged on every reallocation; the offerer's exit consults no contract clause | Kernel/Seat.lean:70-72, 395-402, 471, 550-556, 945; docs/SEATS.md:33-62 |
| status table: landing commits | 2a7c372b, eac4b18c, de9c84f7, 8194e09d, 67362781, d1ce7b0c, bf28dd19, 6347dcb4, 6df4602f, 73223088, a2454432 (`git show --stat` on main) |
| status table: journey rows | scripts/pipeline/journey-rows:15, 40, 65-91 |
| in flight (lane names): activity route, seats native, retention charge, record upgrades, turn gate, laws receiver | OB:381-385; EV:15-19 |

## architecture.html

| Claim | Source |
| --- | --- |
| a signed request; admitted with a receipt or refused with a reason | FRIENDS:81-84 |
| checked against capabilities, laws, exact read roots, funding | README.md:17-20 |
| a computation re-run at admission and on every replay; no admission uses a proof | README.md:180-182; docs/SDK.md:135-136 |
| an Objective invocation: the receiver re-runs the front end on the package, requires a core equal to its own, prices the declared envelope by the tariff, requires the Plan's effects to equal the command's; ran on scratch worlds | OB:299-346; Kernel/ObjectiveBendNativeAdmission.lean:378-400, 468, 578, 650 |
| Selvage outside the deployed umbrella except 12 modules through the digest backend | Deployed.lean:4-9, 14-16 |
| grants with verbs; revocation | FRIENDS:168-173, 231 |
| a law is checked on every change; a law that denies everything is permanent | FRIENDS:186-196 |
| the lock transcript (comments moved to their own lines; the unlock refusal's detail elided) | FRIENDS:190-193 |
| receipt: transaction id, world root, confirmation `installed` / `replayed` / … | docs/SDK.md:18-20 |
| fourteen refusal reasons | Compiler/RefusalReason.lean:56-88; FRIENDS:570-584 |
| a lost reply is a lookup of the same call bytes | docs/SDK.md:79-80 |
| a retry returns the same receipt | FRIENDS:182-184 |
| SDK in Rust and TypeScript, byte-identical | docs/SDK.md:3-5, 90-91 |
| on the device; operator untrusted; member-selected Lean consent process re-derives and returns the header bytes; nothing else is signed | docs/SDK.md:40-47 |
| a browser has no consent process and must not sign until a bridge exists | docs/SDK.md:91-95 |
| private rooms: main only, devnet quality, privacy not audited | FRIENDS:386-388 |
| sealed on the member's machine; key held only wrapped to each member | FRIENDS:389-392 |
| X25519 + ML-KEM-768 wrap | FRIENDS:420-422 |
| the node sees membership, timing, sizes in 64-byte steps | FRIENDS:417-419 |
| founder key trust on first use | FRIENDS:412-415 |
| Generic Simplex BFT engine in Lean, compiled native | README.md:53-55 |
| n = 3f + 1, at most f Byzantine | docs/GENERIC-SIMPLEX-NATIVE.md:11-12 |
| safety over the engine model; liveness not established; four replicas on one host | README.md:80 |

## join.html

| Claim | Source |
| --- | --- |
| accounts by hand; FRIENDS.md is the guide | FRIENDS:1-9, 86-96 |
| make an ssh key; send the public half and a session name; `mini>` prompt | FRIENDS:88-96 |
| works on the node; journey J0–J8 | FRIENDS:13-22; README.md:69 |
| not on the node: rooms, chat, private rooms, key rotation, proxy mode, librarian, paying to enrol | FRIENDS:23-35 |
| pay to enrol: 50 DREGG a week, built, fixtures only, not deployed | FRIENDS:35, 510-540; README.md:84; commits cb4235b6, b0bcb7d0, 243fb343 |
| re-genesis keeps ssh and signing keys and erases what you made | FRIENDS:41-44 |
| hosted key on the box, readable by the operator and, on the single shared account, by other members' sessions; keep nothing precious | FRIENDS:46-52, 62 |
| a split-account setup (only your own account and root read the key) is built and on no box | FRIENDS:53-58; README.md (Split tenancy row); commits 1d4b683f, 73e06411, f991da1d, 7bb016a3 |
| README, AGENTS.md, developer guide; no users; a format change is a rebuild; old shapes refuse; say what breaks | README.md:109-110, 187-192 |
