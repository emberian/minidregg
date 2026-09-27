# Signed GitWeb v2 launch descriptor: offline native qualification

The independent hbox `spk-host qualify-launch` run passed without creating a
Mini Store or launching an app. It parsed the 14,045,864-byte signed GitWeb SPK
once (raw SHA-256 `2bbfe6d3c705dfb0696905ecd9c1d00d6554cc1224e63dc5545152af5f8f2caa`),
then used the pinned Mini Host's pure author and inspect routes. The physical
adapter compared the complete ordered signed create and continue commands,
including argv and environment bytes, with the source inspector's echo.

The result protocol is `mini-spk-launch-qualified-v2`. Its package root is
`87005803221096792113550003106028498326059648433438765766069915491574610318393`,
launch root
`89066044197087243500897137644433855781716276082669749278782223953933431354679`,
and 489-byte canonical descriptor SHA-256
`d5cc3190f8b3fe35209a41d8e2fec181512ffad4482b68085ba9ec8cac723419`.
There is one create command, digest
`33987557079677019429841081848763789461919798002966618578344907189499812660450`;
the continue digest is
`85110639457360734521465147725320505747668551896765509564133951936648792675958`.
These values match the earlier pure Lean author/inspect check, but this run
additionally binds them to one signature-verified physical SPK parse.

The Mini Host ELF was source-qualified from the v2 launch overlay, SHA-256
`4fba53294067013e3f32c012733375bcf51a8ef7895e996d2bdd605bc3c75506`
(builder manifest SHA-256
`1f33c1e529936077b333e91599ff91302360fe574a9c7b0a2aa3559313ee6460`).
The `spk-host` qualifier ELF SHA-256 was
`2819d365dbc50a9becde45e991bf6f035e823073b12d97228407d9a412f30b01`,
built from exact `d513bfa` source archive SHA-256
`9805af2f95c524aca196fcac62f7cf584ad312b1e81468d9b9b2171e7a99f1d3`.
The owner-private offline Mini Settings SHA-256 was
`c7f5e22dc719e732cbd74a24a55df64cf89943b1f485eebc0609344d98564e9b`;
its storage root remained absent. The successful unit was
`mini-spk-launch-v2-positive-r2-20260927.service`, exit 0, 40.96 seconds wall
time, and 364,268 KiB peak RSS.

The first qualifier attempt was preserved as a separate pre-author refusal:
the builder's byte-identical Host image had mode 775, which the offline
image-pin check correctly rejected. The successful attempt used a mode-500
copy in a private directory, with the same Host SHA-256 and a fresh attempt
directory. `r1-stderr.txt` and `r1-verdict.txt` record that distinction.
`result-r2.json` byte-semantically matches retained
`qualification-retained-r2.json`; `launch-inspection-r2.json` echoes the
complete ordered command bytes in `launch-source-r2.json`, and the canonical
binary hashes to the result's `launchCanonicalSha256`. `SHA256SUMS` binds the
selected keyless evidence. This gate establishes descriptor qualification,
not package installation, lifecycle admission, a running resident, or a
dispatchable ticket.
