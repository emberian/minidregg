# Source map for the site

Every factual sentence on the hand-written pages, and the file and lines at main
(`243fb343`, 2026-10-04) it comes from. `status.html` is not listed: it is generated from
`README.md` lines 61-87 by `gen-status.py`, and the `website` gate fails when it is stale.
When a source changes, fix the page and this map in the same commit. Paths are relative to
the repository root. FRIENDS = `deploy/shell/FRIENDS.md`; OB = `docs/OBJECTIVE-BEND.md`.

## index.html

| Claim | Source |
| --- | --- |
| programmable shared world for people and agents; documents, applications, communities and continuing computations share one set of rules | README.md:3-7 |
| a small store of owned resources; every action a signed request the Host (Lean) admits or refuses; receipt; refusal names its reason | FRIENDS:74-77 |
| devnet; re-genesis on data-model or kernel-wire change; everything made goes; no uptime promise | FRIENDS:41-44 |
| public node: 2026-10-01 candidate; shell, documents, boards; no rooms, chat, key rotation, proxy mode; no outside member enrolled | README.md:69 |
| no admission uses a proof; checked by re-execution | README.md:179-180; Deployed.lean:8-9 |
| private rooms devnet quality, privacy not audited | FRIENDS:31, 377 |
| no private execution path runs a member's program privately | README.md:56-58 |
| Lean admits or refuses against capabilities, laws, read roots, funding | README.md:17-20 |
| re-execution at admission and on every replay | OB:244-246; docs/SDK.md:110 |
| Rust supplies clients, signing and custody, storage, transport, hosted-service adapters; decides nothing semantic | README.md:19-21 |
| a law is checked on every change; a lock stops owner and operator | FRIENDS:179-187 |
| computation proposes; authority admits; reference is not ownership; lost reply keeps the original operation | README.md:22-24 |
| Objective Bend: lazy, first-class partial composable specifications, after Faré | OB:3-6 |
| soundness, preservation, completeness proved; not re-checked by the default build | OB:176-192, 227-233; README.md:73 |
| no Objective Bend program admitted by a native Host | OB:298-299; README.md:74 |
| design aim: inspect tools, compose behaviour, delegate bounded work, no unrestricted access | README.md:7-9 |
| friends use the hosted shell | FRIENDS:1, 79-93 |
| useful contributions list | README.md:187-189 |
| product is Mini; repo and host binary keep minidregg | README.md:1, 147 |

## language.html

| Claim | Source |
| --- | --- |
| Mini's authored language; Faré's account; lazy open recursion over first-class, partial, composable specifications | OB:3-6 |
| Mini supplies identity, authority, effect admission, funding, disclosure | OB:6-8 |
| Core4 is `Term` in `Theory/ObjectiveBendOpenRecursion.lean` | OB:43-44 |
| call-by-name reference semantics; call-by-need machine with shared heap thunks | OB:51 |
| laziness is part of the meaning; `{good = 7, bad = self.bad}.good` is 7; unused divergent argument never forced | OB:35-37 |
| specification `C → V → W`, final self, whole super; a value before any target | OB:20-24 |
| `mix` formula; `fix` is a computation | OB:30, 33-35, 52-53 |
| prototypes; `reflect`/`metadata`/`project` without forcing | OB:38-39, 55-56 |
| records of suspensions; `extend`; sums | OB:59-63 |
| activities yield a typed Plan and are resumed; effects are a type; never inside a shared thunk | OB:64; docs/OBJECTIVE-BEND-EVENTS.md:80-92, 106 |
| proof-producing checker; quantities; at most once | OB:67-75 |
| TypeScript front end is a trusted boundary; no source-to-core theorem | README.md:96-97; OB:214-215, 309-312 |
| example 1 file | docs/tutorial/ch4-specs.obend (whole file; checked by the `website` gate) |
| example 1 output | docs/OBJECTIVE-BEND-TUTORIAL.md:590-604 (checked by the `website` gate) |
| bill is 7 without Surcharge, 9 with it | docs/OBJECTIVE-BEND-TUTORIAL.md:607-609 |
| example 2 file | docs/tutorial/ch8-counter.obend (whole file; checked by the `website` gate) |
| example 2 output | docs/OBJECTIVE-BEND-TUTORIAL.md:1001-1008 (checked by the `website` gate) |
| turn 3 refused, turn 4 repeats; responses typed by hand; nothing admitted | docs/OBJECTIVE-BEND-TUTORIAL.md:1011-1013; docs/OBJECTIVE-BEND-EVENTS.md:141-144 |
| no kernel delivers responses or persists an activity | docs/OBJECTIVE-BEND-EVENTS.md:12-13 |
| the tutorial gate re-runs every command block | scripts/check-objective-frontend.sh:19-20 |
| axioms pinned to propext, Classical.choice, Quot.sound; no sorry, axiom, native_decide, partial, extern | OB:172-174 |
| theorem table rows (soundness, preservation, no refusal, completeness, data soundness, activities) | OB:180-191; docs/OBJECTIVE-BEND-EVENTS.md:105-110 |
| completeness has no resource bound | OB:199-202 |
| uniqueness of deep data not proved | OB:209-211 |
| fast machine theorems, `@[csimp]`, axioms `[propext, Quot.sound]`; every compiled call runs it | docs/OBJECTIVE-BEND-BACKENDS.md:17 |
| 14,885 ms → 41–43 ms (StressWork, 524,293 ticks); 37,684 ms → 36–292 ms (StressCount, stack ≈20,000, loaded box) | docs/OBJECTIVE-BEND-BACKENDS.md:44-45, 60-61 |
| proofs imported only by the opt-in research library; green default build re-checks none | OB:227-233 |
| `OrderedPresentationInvariant` stated, not proved; C4 in the elaborator | OB:131-137, 212-213 |
| quantities static only | OB:216-217 |
| no native accepted receipt; modules compiled in lanes; caller-chosen `proofWork`, zero is free up to the policy maximum | OB:298-304 |
| Studio preview route wire-broken (v1 vs v2) | OB:264-267 |
| backends table | docs/OBJECTIVE-BEND-BACKENDS.md:14-21; OB:333-339 |
| 340/340 differential cases; four mutants caught | docs/OBJECTIVE-BEND-BACKENDS.md:16 |
| no `- < > <= >= /`; Nat match two branches; no sum wildcard | OB:374-377 |
| subtraction by recursion | docs/OBJECTIVE-BEND-EVENTS.md:177-178 |
| `requires` unchecked; laws undischarged; `before`/`after` refused | OB:222-223, 381-382 |
| Plans and responses non-recursive, so no view library | docs/OBJECTIVE-BEND-EVENTS.md:176-177 |

## architecture.html

| Claim | Source |
| --- | --- |
| Lean owns semantics and admission; Rust the physical boundary | README.md:17 |
| the diagram, and that it is a contract, not a wiring claim | README.md:26-38; docs/README.md:40-41 |
| admission against capabilities, laws, read roots, funding | README.md:17-20 |
| re-execution at admission and on replay at reopen | OB:244-246, 297-298; docs/SDK.md:110 |
| no admission uses a proof | README.md:179-180; docs/SDK.md:111 |
| deployed umbrella leaves out proof-system research; Host still imports 12 Selvage modules via a digest backend | Deployed.lean:6-9, 13-16 |
| Selvage description; research | README.md:176-180 |
| Rust side list; decides nothing semantic | README.md:19-21 |
| one Store = directory + key file + head anchor outside; SQLite log | docs/DURABLE-STORE.md:3-4, 13-15 |
| KMAC tags on log entries and checkpoints; what a valid tag does and does not mean | docs/DURABLE-STORE.md:22-33 |
| resource: governed state with exact representation and history | docs/README.md:50 |
| delegate a grant with verbs; revoke; `refused: revoked` | FRIENDS:163, 221-222 |
| JSON laws; one-line grammar on main; Host checks satisfiability on main | FRIENDS:187-197, 587-588 |
| lock transcript | FRIENDS:181-184 |
| nobody can bypass, owner or operator | FRIENDS:186 |
| capability and law not replaced by a reference | docs/README.md:51 |
| receipt fields | docs/SDK.md:18-20 |
| refusal reasons | FRIENDS:563-581 (Compiler/RefusalReason.lean) |
| lost reply → lookup of the same call bytes | docs/SDK.md:77-78; README.md:23-24 |
| retry returns the same receipt, `replayed`, same transaction id | FRIENDS:173-175 |
| SDK crates; TS byte-identical to the Rust core | docs/SDK.md:3-5, 88-89 |
| SDK surface diagram | docs/SDK.md:10-14 |
| runs on device; key never leaves; member-selected Host and consent executable; operator untrusted; Lean consent re-derives; SDK signs only those bytes | docs/SDK.md:39-46 |
| confirmation binds invocation, attempt, intent, plan, headers, reading | docs/SDK.md:79-80 |
| browser has no consent process; must not sign until a bridge exists | docs/SDK.md:90-93 |
| private rooms: main only; no run on a real Host recorded; devnet quality; privacy not audited | FRIENDS:31, 377 |
| a room is a resource things are born in | FRIENDS:284 |
| sealed on the member's machine; node holds key wrapped to each member | FRIENDS:379-381 |
| X25519 + ML-KEM-768 wrap; founder signatures not post-quantum | FRIENDS:411-413 |
| kick: revoke + fresh key; keeps what was readable | FRIENDS:398-400 |
| node sees membership, timing, size in 64-byte steps | FRIENDS:408-409 |
| founder pin trust on first use | FRIENDS:379, 403-405 |
| a misbehaving node can hide a key change until seen once | FRIENDS:409-411 |
| hosted shell keeps member key and room key on the box | FRIENDS:382-383 |
| Generic Simplex BFT engine in Lean, compiled native | README.md:53-55 |
| n = 3f + 1, at most f Byzantine, authenticated reliable delivery, partial synchrony | docs/GENERIC-SIMPLEX-NATIVE.md:10-12 |
| safety theorem over the engine model; four replicas, one host, one failure domain; liveness not established | README.md:78 |
| four-node harness with TCP, ML-DSA, Byzantine COMMIT delivery, certificate recovery, lost CAS replies | docs/GENERIC-SIMPLEX-NATIVE.md:4-7 |
| membership change separate; workdesk fixture not run | docs/GENERIC-SIMPLEX-NATIVE.md:8, 13-14 |
| SPK | README.md:48-49, 75 |
| Hermes | README.md:50-52, 76 |
| traffic privacy | README.md:56-57, 79 |
| MPC / FHE | README.md:80 |
| not done: Objective receipt; activity delivery; proofs not in default build; chat; Studio; payments; private execution; agreement | OB:298-299; docs/OBJECTIVE-BEND-EVENTS.md:12-13; OB:227-233; README.md:71, 72, 82, 57-58, 78 |

## join.html

| Claim | Source |
| --- | --- |
| the guide is FRIENDS.md; it says per section what the node has | FRIENDS:1-9 |
| accounts by hand: ssh key, public half, session name; `mini>` prompt | FRIENDS:79-93 |
| pay to enrol designed, not deployed | FRIENDS:501-506; README.md:82 |
| what the node has (verbs, documents, boards, JSON laws, lock, retry, history) | FRIENDS:13-22; README.md:69 |
| passed the shell journey J0-J8 | FRIENDS:22 |
| what the node lacks | FRIENDS:23-35 |
| devnet; re-genesis keeps ssh and signing key, loses what you made; no uptime promise | FRIENDS:41-44 |
| hosted key readable by the operator and every process of the box's account, including other sessions; keep nothing precious | FRIENDS:46-52 |
| contributing: README, AGENTS.md, developer guide; no users or compatibility obligation; old shapes refuse | README.md:107-108, 189-191 |

## Runs behind the examples

At `243fb343` on 2026-10-04, `bun scripts/check-objective-tutorial.ts` printed
`TUTORIAL PASS: 61 commands reproduce the tutorial's printed output`, with the eight
modules `Host/ObjectiveBendPreview.lean` imports compiled by `lean -o` (Lean 4.30.0).
