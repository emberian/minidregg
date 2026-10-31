/-
# Fixtures.NativeDocWriteFixtureAuthority -- the HAND-WRITTEN authority of the native document-write fixture

No generator writes this module.  It states what the member ASKED FOR
(`native/resource-client/doc-write-native-acceptance.py`: `doc new paper draft`, then
`doc append a1 paper 'first paragraph'`, then `doc append a2 paper 'second paragraph, appended by
the same member'`, the calls `mini shell` makes), as `key = value` lines, never what a run produced.
`Fixtures.NativeDocWriteFixture.write_projection` checks the re-run's projection
(`Fixtures.NativeDocWriteFixtureProjection`) against it, and
`scripts/native-doc-write-fixture/generate.sh` refuses to write data whose projection differs.
Changing it is its own commit with an `Authority-Change: <reason>` trailer
(`scripts/pipeline/check-fixture-authority.sh`).
-/
namespace Minidregg.Fixtures.NativeDocWriteFixtureAuthority

/-- The authority lines. -/
def text : String := "
# AUTHORITY for Fixtures.NativeDocWriteFixture -- HAND-WRITTEN. No generator writes this file.
# It states what the member asked for, read from native/resource-client/doc-write-native-acceptance.py
# and the shell's `document_proposal` (native/resource-client/src/shell.rs), never from a run.
# Changing it is its own commit with an `Authority-Change: <reason>` trailer
# (scripts/pipeline/check-fixture-authority.sh).

# the second `doc append` (a2): one workspace proposal, action invoke, one target (`paper`)
write.verdict = accepted
# signed by the sponsor, subject '7' (the only member of the scratch world)
write.subject = (some 7)
write.targets = 1
# one signed envelope per incidence: the authority leg and the one target leg
write.receipts = 2
write.receipts.signedBySubject = true
# the only cell written is the document's content cell (registry tag 1): no pay-cell write
write.writes = tag1
write.writes.targets = true
# the authority cell is read, never written; no written cell is also guarded
write.guards.authorityCell = true
write.guards.writtenCells = false
# one invocation marker spent
write.nullifiers = 1
# the document holds exactly the text the member appended, nothing else:
# 'first paragraph' (15 bytes) + 'second paragraph, appended by the same member' (45 bytes)
write.document.payloadBytes = 60
# The byte lines are relations to the run, never numbers: the call, the digests and ids it carries
# and the values it writes are encoded at their natural width, so their lengths move by a few bytes
# from run to run (recordings with 1015- and 1013-byte calls), and the ingress framing moves with
# the width of the semantics digest. The retained event is exactly the call's signed ingress (the
# deployment's domain, the semantics and the signed command, DeclaredResourceController.signedBytes).
write.event = ingress
# the World's leg on the document cell, by operation (reads carry no bytes): two writes and two
# allocations, one of them the atom holding the appended paragraph
write.legs = read, read, read, write, write, allocate, allocate
# an append is not metered compute and pays no fee in this world: only the structural lanes move.
# The incidences are the authority leg and the one target. The other three lanes are the Host charge
# rule's measurements of this write (DeployedCharge, 7877e6e7): the call's turn bytes (the length of
# its signed ingress), the retained bytes (exactly the event plus the leg's written values:
# no post image, no framing), and the cells touched.
write.charge.incidences = 2
write.charge.turnBytes = ingress
write.charge.memoryTouches = 6
write.charge.storageBytes = event + legs
write.charge.witnessBytes = 0
write.charge.proofWork = 0
write.charge.feeDebit = 0
write.charge.networkBytes = 0
write.charge.sideEffectCount = 0
write.charge.leaseByteBlocks = 0
"

end Minidregg.Fixtures.NativeDocWriteFixtureAuthority
