# Resident final delivery

A completed model turn and a delivered room reply are separate facts. The source
resident driver drains a pending final reply before its prompt limit or unchanged
input check, without invoking a model again.

The controller binds the exact source resident origin and assignment to the last
settled, metered provider response. New turns additionally compare the final
assistant text captured directly from ACP with the retained terminal SSE response.
The historical receiver explicitly records that it uses a settled provider final
and an already retained authoritative completed resident frame; it does not claim
an ACP text capture that did not exist then. Display output never supplies evidence.

For an addressed assignment, routing selects the latest entry for one recipient;
multiple addressed recipients require explicit routing. It retains the full signed
entry tuple and refreshes its merged feed number. The actual Mini say command
checks that number still resolves to the expected stream cell and sequence before
submission. Model content is published as model content, never as a signed view.

The durable residentDelivery marker precedes its sidecar and the clearing of the
old session pending fence. It blocks another prompt, unrelated writes and ordinary
configuration migration, and participates in the shared quiescence inventory.
Historical strict Journal readers refuse the new active marker. A preallocated
room operation ID then enters the existing ToolTask reservation, Book turn payment
and immutable native operation-record receiver. Recovery looks up that exact
operation; it never invents a replacement payment or message. A prior progress
message suppresses nothing: deduplication requires this origin, exact final text,
recipient, reply and performed native result.

Operator interface:

    grain-runtime resident-delivery plan ADMIN_SOCKET RESIDENT_STATE_DIRECTORY
    grain-runtime resident-delivery deliver ADMIN_SOCKET PRIVATE_REQUEST

The plan reports the exact final, recipient, stable source entry, current reply
number, resident byte hash and plan hash. The request has type
mini-resident-delivery-request-v1 and fields residentState, residentSha256,
planSha256 and replyEntryNumber. The receiver holds the resident lock and freshly
checks physical, signed native and session closure before writing. Its typed
mini-resident-delivered-v1 receipt is retained before clearing the marker.

The current bridge accepts one final of at most the existing 3000-byte room-tool
limit. It refuses oversize output rather than truncating or splitting it into
untracked messages. Its receiving tests cover marker/sidecar failure, pre/post-ID
cuts, confirmed room recovery, receipt-before-marker-clear and wrong-origin or
progress-message suppression. These are source receiving tests, not claims of a
native crash at every cut. Native delivery and restart/retry evidence is recorded
separately. A crash before the resident receives its model-turn completion remains
fenced until the separate typed completed-turn receiver is joined; it must never
be worked around by replaying the model prompt or editing completion counters.


Ordinary model-issued says without an old expectedReply field can now recover
stable thread identity automatically. The source client operation-proof command
validates and exact-lookups the original signed append, with no new write. The
receiver verifies its original and retained evidence hashes, origin/content/to,
and stable cell/sequence; it enriches a copy of the resolution and archives that
proof, preserving the original resolution. An equal positional number alone never
suppresses another reply. Opaque private-room payload proof still refuses pending
shared decryption/binding support. Three client tamper tests and actual operation396
native proof passed; twelve delivery tests cover receiving identity/renumbering
and wrong proof rejection. Live304 already had its guarded receipt and is unchanged.
