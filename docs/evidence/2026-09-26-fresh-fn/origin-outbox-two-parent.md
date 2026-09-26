# Two prepared R parents in one accepted Mini catalog

The pure `scripts/probe-fn-origin-outbox.lean` check constructed two distinct
prepared R records with different original signed calls and Message-IDs. With
both records in one accepted-history list, `selectUniqueParent` returned the
matching record for either parent ID. The same run checked exact historical
reopen, an exact retry without a second write, refusal of changed content
under one Message-ID, refusal of altered target kind, and refusal of an
ambiguous duplicate parent. Bounded output:
[origin-outbox-two-parent.log](origin-outbox-two-parent.log).

Probe SHA-256 `23adcd09af6d1a3f6411d41551dee8da5f107e64ee97d331060b7ae17c4c4f83`;
log SHA-256 `aee198ef516971919d22ea2555f0c1cd51617c2830dbff755cdbcc02dcdb4876`.

This is a pure selector check with synthetic carriers. A live two-R fn/Mini
exchange remains separate evidence.
