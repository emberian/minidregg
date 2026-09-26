# Selected-profile prepared R outbox capacity

`scripts/probe-fn-origin-outbox-max.lean` ran in an independent warm Mini
snapshot against `Kernel/FnOriginOutbox.lean`. It constructed one prepared R
record with a synthetic carrier of exactly 1,516,384 bytes, the selected
`FnEvidenceCodec.maxCarrierBytes`, and checked the actual
`ContentResource.preparePage` result. It also strictly decoded the full signed
command and compared its exact canonical bytes.

Result: PASS. The prepared atom encoded to 1,518,636 bytes, the signed command
to 1,518,765 bytes, the observation intent to 1,518,853 bytes, and the materialized
page content to 1,518,729 bytes. The selected native host frame cap was
6,194,884 bytes. The bounded output is [origin-outbox-max.log](origin-outbox-max.log).

Source SHA-256: probe `bf7d113a4c94ac47a862f3422edd1e339058b31ff8ebe87d41cc39745155dd0d`;
`Kernel/FnOriginOutbox.lean` `5fb063ab84b78920aa455563a69672e1cd9bee9149c56de342d9401473170387`;
log `947cdb29457b09eb4141b3e28cb126635eff725c8cef8e70b23f2f033dd47834`.

This is a pure size/materialization check with synthetic carrier bytes. It does
not claim native fn authorship, receiving admission, or an op16 JSON frame
measurement.
