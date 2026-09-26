# Actual Hermes ACP through the Mini provider gateway

An unmodified upstream Hermes ACP worker ran inside the grain sandbox on a fresh
Mini parent task 7201. The controller used a generated Hermes provider profile
pointing to its local gateway, which forwarded only to the deterministic loopback
protocol fixture. No paid provider or real credential was used. The fixture
received exactly three completion requests, in order: read the named
`publication` resource, publish scalar field 0 with value 1 using that signed
read's root, and return final text. `provider.log` records only bounded request
metadata. The final ACP text in `client-hold.stdout` says the Mini read and
publish tool calls completed.

Each request was held until a signed provider reserve and parent witness were
confirmed; `provider-reserve-1-source.json` shows the first exact joint intent
with provider task 7204 and parent witness task 7201. The fixture log had zero
requests before the first reserve. The
three configured fixed provider charges settled at Mini accepted counts 11,
15, and 23. The durable final journal projection contains three byte-exact
cached HTTP 200 responses and no pending provider request or hold. These are
protocol-fixture results, not evidence of model quality or live provider
custody.

Hermes registered the three actual `mini-grain` MCP tools. Its signed resource
read took 63.51 seconds; its `mini_publish` tool returned a result after 284.01
seconds. The joint publication call in `tool-settle-call.bin` was confirmed at
Mini accepted count 19. An independent signed capability-94 read returned
object 7003 root
`55070908931993074135985362517665169451634431671625479692889086081017559966815`
with field 0 = 1. The worker returned final ACP text and the parent fixed
charge settled at accepted count 25. The final journal has no child, pending
operation, settlement, hold, or unresolved external effect; its upstream
session ID and SQLite fingerprint remain retained with `pendingPrompt=false`.

The Linux Mini host was the certified combined binary SHA-256
`31a00492594a9abbde4541fef687f4d6a2fd2cac06c1645e604178a3e7f18179`.
The controller and sandbox MCP proxy were identical Linux binaries SHA-256
`173cb9a6b14aca36f2c232c96e88d54c4355f5be67695b91f05360068b7ee1d6`,
built from frozen runtime main source SHA-256
`d58fc4ecc5ea8fc1c203c88a39407ef49c74e9e24a02c6466a2f7d8e8c5876ae`
and provider source SHA-256
`92d62913587c71dd87e7b94673bdd6c3dd1c5152f6b9b2c9829951f7f1835a43`.
The local fixture binary SHA-256 was
`eb39042732749593fef4ed51269f0a2565b48d961f8403f9acb0d86d69277c24`.
The persistent Mini host socket was owned by an isolated task-7201 service;
the Hermes worker had a 1500-second wall limit.

The retained raw journal SHA-256 is
`7c8e7924dc41b4d408dea0033d3cb8584b5314fe4c27fc0399604338d3824792`;
its full binding and private runtime config are omitted here. The private
runtime config SHA-256 is
`2aeaab7bb2a9410d7ff56e076358e9f019f06dc80ea546b0f2a7d524a96fc740`.
The exact joint call SHA-256 is
`13f445178b587ad38ffd6326ea1841ddff16f6ca388daa009701507ccefdb707`;
its confirmed outcome SHA-256 is
`f7d81f1fbcbbbed7fd3a1a13034e64006bad71d8d0f211a4fd8c03e29e4d9b67`.
The signed final view and challenge are preserved as `.bin` files alongside
their decoded view; `native-outcomes.json` lists the selected Mini accepted
counts. No private key, provider token, full request body, or raw config is
included.
