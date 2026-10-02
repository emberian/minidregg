# Native Host request allocations

`protocol/host-operations.json` is the allocation record. Every request byte has
one stable symbol, owning subsystem, purpose, receiving entry point, status and
intended socket routes. Active entries must match actual source. Reservations
have no receiver yet and may not appear in a shipped dispatcher or allowlist
until explicitly promoted. A branch must reserve its byte here before using it;
Git integration and the gate reject duplicate reservations, including a newly
proposed operation colliding with an older family such as job-money 160–163.

Run from the repository root:

```
python3 scripts/host-operations.py generate
python3 scripts/host-operations.py check
python3 scripts/test-host-operations.py
```

`generate` validates the allocation record and rewrites only the deterministic
shared Rust constants, then performs the source consistency check. It does not
infer allocations from arbitrary numbers, silently promote a reservation,
change socket exposure, or rewrite receiving code. `check` changes no files.
Both the ordinary local/CI gates and the native builder run the checker; the
ordinary gate additionally runs mutation tests. There is no Lean compilation
in this check.

For a new operation:

1. Add a unique reserved entry with an unused request byte and stable symbol,
   an owner/purpose and intended routes. Public requests list both `public` and
   `operator`, since the owner-private Host endpoint also serves filtered public
   ingress. Operator-only operations list `operator`. An empty route list means
   Host stdio only, not an implicit public route.
2. Generate the constants and commit the reservation. Use the shared constant
   from Rust additions where practical, for example a module declared with
   `#[path = "../../host-operations.rs"] mod host_operations;` in a native
   crate's `src/main.rs`. The generated file contains request constants only.
3. Implement the source receiver and the intended central transport selector.
   Promote the entry to `active` and name its actual `serveFrame`,
   `dispatchSession`, or `fnDispatch` receiver in the same change. Register
   explicit client `u8` constants under `client_constants` when a separate
   transport client owns one. Numeric and generated-symbol references are
   checked against the same allocation.
4. Run the consistency and mutation checks, then the operation's actual
   receiving tests. These are different obligations.

The scanner understands the current three-layer Host dispatcher and the two
central Rust slice-pattern allowlists. It masks strings, character literals,
raw strings and nested comments, balances Rust delimiters, expands literal
request ranges, detects duplicate/shadowed arms and verifies direct dispatch
boundaries. The frame interceptor accepts only literal equality tests joined by
`||`. An exact `fnDispatch operation payload` arm is a delegation edge whose
receiving owner must exist in `fnDispatch`; changed arguments or additional logic
remain concrete arms and cannot silently shadow another receiver. Unknown
dispatcher shapes fail closed and require a reviewed parser update. It scans only the request selector in these named dispatch structures
and explicitly registered client constants. It does not scan response literals,
arbitrary `invoke` arguments, nested codec tags, documentation numbers or all
integers in the tree.

`response_markers` are a separate namespace. A marker reserves a request byte
only when `request_reserved` is explicitly true (transport refusal 254 and Host
refusal 255). Request 164 may legitimately receive response 34, and request 34
may receive the definitive no-record response 164. Ordinary responses echoing
their request byte are also not duplicate allocations. This gate does not claim
to verify response codecs, payload guards or Mini authorization; those remain
source admission and runtime receiving-test responsibilities.

The joined source inventory retains Host-only operations 24/25 for selected-source
publication. Observer-signed enrollment 117–120 is operator-only; public quote
121 has its bounded JSON-object guard. Stream renewal 152, route inspection 154
and route-bound dispatch 164 remain private. Exact carry receipt recovery 153,
paid-claim operations 181–186 and next-key adoption 187–190 have bounded public
selectors. Their registry status records installed source and routing, not an
independent claim of native runtime qualification.

Carried paid-claim receipt lookup 191 and same-image law diagnostic 192 remain
reserved without receivers or endpoints. A route-changing integration must
update the record with receiving code and tests; changing the record to match
an unintended exposure does not establish authorization.
