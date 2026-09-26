# Direct Mini ContentResource smoke, 2026-09-26

This bounded subset records a fresh **singleton** Mini content object 8001
create/edit/read cycle. It is not a grain-held joint publication, an upstream
Hermes turn, or an fn transfer. `scripts/workroom/probe-content.sh` SHA-256
`18739fae1dac154bd4eb9d330ce9fa80dfdbb1c0f17bece93982b01a389ba192`
authored the two fixed untrusted text payloads, while the native Lean Host
authored/admitted the signed operations. The provisioning script at execution
was the pre-parameterization version, SHA-256
`bea8e6f3a45894782dab5cb632fa40e1d6e14521ba7d2c4791e54c26ee314292`.

The fresh scratch deployment was
`/tmp/mini-workroom-provision-20260926-b` with pinned config SHA-256
`a6d0d16cbf9f868717ec168f493735aa219153c952e70e29926d5a53bade6470`.
The executed Mac Host was
`/tmp/minidregg-overnight-20260926/minidregg-host-catalog`, SHA-256
`9a42dca4e181ad67c3de469fdb1f14d5649fb9cddc80fc6e88b4dd386cbb9dbe`.
The Mini client was the mutable
`native/resource-client/target/debug/mini`; its execution-time binary hash
was not captured. No key, pinned config, Store, or full session is copied
into this evidence subset.

The initial signed observe-capability-96 read had an empty page at root
`97349327118568466779609446662939988221287696762075284738918673226692685974561`.
`create-call.bin` installed with acceptedCount 7 and created text atom 7401;
the next signed read had root
`43588760809796208894087654721232400529460114370049589776250449143074108380498`.
`edit-intent.json` used that read's complete old AtomRecord as `before`.
`edit-call.bin` installed with acceptedCount 8; the final signed read had
root `20054374654993399460178461963856436968479637091184470350422277389653408733371`
and exactly one atom with the revised text. The three `view.bin` and
`signed-observation.bin` pairs retain the selected native query bytes; the
JSON views are their readable presentations. `SHA256SUMS` covers every
copied file.

The full private attempts, deployment, and Store remain under the two `/tmp`
paths above. Re-verifying the historical signed calls requires that private
physical scope; the subset alone is an exact-byte audit sample, not an
independent replay certificate.
