# kern gate contract review

Baseline: pinned manifests at `8e37e22d`; source attribution range `aaf89764..8e37e22d`.
The full objective gate and all its mutation self-tests passed in draft mode (j500951450).
Retained scans (j501102289), followed by the hash audit (j501347896), classify:

| Class | Rows |
|---|---:|
| Added | 495 |
| Pure moves: same key, statement, closure and axiom set | 313 |
| Unchanged statement, changed definition closure | 8366 |
| Restated | 89 |
| Removed keys | 24 |

445 surviving declarations moved module and also changed statement or closure; these are **not** pure moves.
The 313 pure moves are recorded individually in `gate-pure-moves.tsv`: 127 DurableReceiverCore,
114 ObjectiveActivityReceiverCore, 48 SeatReceiverCore, 22 DurableHistoryStoreCore, 2 PayAssignmentOwner.
The gate checks every exact old/new contract hash; `objective-contract-changes.txt` individually names
all 8479 non-pure changes and records their reason classes and commit attribution.

Most changed closures arise from the merged generation inbox/schema-refs v6 change (079ff7ea),
R0 absence guards and stateRetired (8aacd180, 3b24dcf7), the charged-refusal byte codec (775240ec),
and the R2 checked writer and Core extraction (de1a3a33). The 49 initially unattributed JobMoney/PurseRefill
rows reach the relocated PayAssignmentOwner private match splitter; OwnerTargets and OwnerGrant source
bodies are unchanged. The audit records those exact dependencies, not a blanket semantic-change waiver.

The 24 removed keys comprise 22 private declarations relocated to Core (20 unchanged statement hashes;
two hash shifts due to relocated private constant references), Loaded.judge_tail (replaced by
Commit.tail_pinned/Judged.tail_pinned, with tail-law conclusion retained in advance_judged), and
encodableOfLawful (the exponential Nat encoding helper removed by the byte-codec change).
Each private successor is validated by the regular gate.

ResearchWip.lean and SimplexQualification.lean were rewritten only by
`scripts/lean-build-surfaces.py generate`; both have zero diff. The surface JSON is that generator's
output; this range does not regenerate or edit NativeAcceptedFixtureData.lean.

The seven hypothesis-ledger entries remain open pole findings. No claim is made that those premises
are discharged: the ledger states the conditional evidence and outstanding closed positive/negative instances.

## Individually restated declarations

- `Minidregg.Compiler.DurableCheckpointCodec.seedEpoch_spentMap_refused` — 079ff7ea: pole schema-refs/v6: seed-epoch refusal now also diagnoses schema-refs/v5 versus v6.
- `Minidregg.Compiler.DurableReceiverIO.Loaded.judge` — de1a3a33: R2 checked commit API: judge returns indexed evidence, writer/replay consume it, and route/source theorems retain conclusions under Judged evidence.
- `Minidregg.Compiler.DurableReceiverIO.publish` — de1a3a33: R2 checked commit API: judge returns indexed evidence, writer/replay consume it, and route/source theorems retain conclusions under Judged evidence.
- `Minidregg.Kernel.Inbox.Fifo.pop` — 079ff7ea: pole generation inboxes: preserve generation across FIFO steps and use snapshot-selected generation cells with exact generation evidence.
- `Minidregg.Kernel.Inbox.Fifo.push` — 079ff7ea: pole generation inboxes: preserve generation across FIFO steps and use snapshot-selected generation cells with exact generation evidence.
- `Minidregg.Kernel.Inbox.Inbox.empty` — 079ff7ea: pole generation inboxes: preserve generation across FIFO steps and use snapshot-selected generation cells with exact generation evidence.
- `Minidregg.Kernel.Inbox.Inbox.mk` — 079ff7ea: pole generation inboxes: preserve generation across FIFO steps and use snapshot-selected generation cells with exact generation evidence.
- `Minidregg.Kernel.Inbox.Step.pop` — 079ff7ea: pole generation inboxes: preserve generation across FIFO steps and use snapshot-selected generation cells with exact generation evidence.
- `Minidregg.Kernel.Inbox.Step.push` — 079ff7ea: pole generation inboxes: preserve generation across FIFO steps and use snapshot-selected generation cells with exact generation evidence.
- `Minidregg.Kernel.Inbox.Step.withdraw` — 079ff7ea: pole generation inboxes: preserve generation across FIFO steps and use snapshot-selected generation cells with exact generation evidence.
- `Minidregg.Kernel.Inbox.cell` — 079ff7ea: pole generation inboxes: preserve generation across FIFO steps and use snapshot-selected generation cells with exact generation evidence.
- `Minidregg.Kernel.Inbox.cell_reserved` — 079ff7ea: pole generation inboxes: preserve generation across FIFO steps and use snapshot-selected generation cells with exact generation evidence.
- `Minidregg.Kernel.Inbox.key` — 079ff7ea: pole generation inboxes: preserve generation across FIFO steps and use snapshot-selected generation cells with exact generation evidence.
- `Minidregg.Kernel.Inbox.reorder_unfifo` — 079ff7ea: pole generation inboxes: preserve generation across FIFO steps and use snapshot-selected generation cells with exact generation evidence.
- `Minidregg.Kernel.Inbox.reorder_unlawful` — 079ff7ea: pole generation inboxes: preserve generation across FIFO steps and use snapshot-selected generation cells with exact generation evidence.
- `Minidregg.Kernel.Inbox.sample_full` — 079ff7ea: pole generation inboxes: preserve generation across FIFO steps and use snapshot-selected generation cells with exact generation evidence.
- `Minidregg.Kernel.Inbox.sample_push_pop` — 079ff7ea: pole generation inboxes: preserve generation across FIFO steps and use snapshot-selected generation cells with exact generation evidence.
- `Minidregg.Kernel.Inbox.sample_withdraw` — 079ff7ea: pole generation inboxes: preserve generation across FIFO steps and use snapshot-selected generation cells with exact generation evidence.
- `Minidregg.Kernel.NativeHostReplay.ExactReadback.judged` — de1a3a33: R2 checked commit API: judge returns indexed evidence, writer/replay consume it, and route/source theorems retain conclusions under Judged evidence.
- `Minidregg.Kernel.NativeHostReplay.ExactReadback.mk` — de1a3a33: R2 checked commit API: judge returns indexed evidence, writer/replay consume it, and route/source theorems retain conclusions under Judged evidence.
- `Minidregg.Kernel.ObjectiveActivity.Refusal.awaitingRebirth.elim` — 3b24dcf7+079ff7ea: R0 stateRetired refusal added; generated constructor eliminator index changes.
- `Minidregg.Kernel.ObjectiveActivity.Refusal.domainCodec.elim` — 3b24dcf7+079ff7ea: R0 stateRetired refusal added; generated constructor eliminator index changes.
- `Minidregg.Kernel.ObjectiveActivity.Refusal.domainExists.elim` — 3b24dcf7+079ff7ea: R0 stateRetired refusal added; generated constructor eliminator index changes.
- `Minidregg.Kernel.ObjectiveActivity.Refusal.domainLawDenied.elim` — 3b24dcf7+079ff7ea: R0 stateRetired refusal added; generated constructor eliminator index changes.
- `Minidregg.Kernel.ObjectiveActivity.Refusal.domainMember.elim` — 3b24dcf7+079ff7ea: R0 stateRetired refusal added; generated constructor eliminator index changes.
- `Minidregg.Kernel.ObjectiveActivity.Refusal.domainMissing.elim` — 3b24dcf7+079ff7ea: R0 stateRetired refusal added; generated constructor eliminator index changes.
- `Minidregg.Kernel.ObjectiveActivity.Refusal.domainShape.elim` — 3b24dcf7+079ff7ea: R0 stateRetired refusal added; generated constructor eliminator index changes.
- `Minidregg.Kernel.ObjectiveActivity.Refusal.domainUncovered.elim` — 3b24dcf7+079ff7ea: R0 stateRetired refusal added; generated constructor eliminator index changes.
- `Minidregg.Kernel.ObjectiveActivity.Refusal.domainUnindexed.elim` — 3b24dcf7+079ff7ea: R0 stateRetired refusal added; generated constructor eliminator index changes.
- `Minidregg.Kernel.ObjectiveActivity.Refusal.domainUnprojectable.elim` — 3b24dcf7+079ff7ea: R0 stateRetired refusal added; generated constructor eliminator index changes.
- `Minidregg.Kernel.ObjectiveActivity.Refusal.domainsDropped.elim` — 3b24dcf7+079ff7ea: R0 stateRetired refusal added; generated constructor eliminator index changes.
- `Minidregg.Kernel.ObjectiveActivity.Refusal.drainPatience.elim` — 3b24dcf7+079ff7ea: R0 stateRetired refusal added; generated constructor eliminator index changes.
- `Minidregg.Kernel.ObjectiveActivity.Refusal.draining.elim` — 3b24dcf7+079ff7ea: R0 stateRetired refusal added; generated constructor eliminator index changes.
- `Minidregg.Kernel.ObjectiveActivity.Refusal.fieldsForgotten.elim` — 3b24dcf7+079ff7ea: R0 stateRetired refusal added; generated constructor eliminator index changes.
- `Minidregg.Kernel.ObjectiveActivity.Refusal.floorNotEntailed.elim` — 3b24dcf7+079ff7ea: R0 stateRetired refusal added; generated constructor eliminator index changes.
- `Minidregg.Kernel.ObjectiveActivity.Refusal.frozen.elim` — 3b24dcf7+079ff7ea: R0 stateRetired refusal added; generated constructor eliminator index changes.
- `Minidregg.Kernel.ObjectiveActivity.Refusal.lawField.elim` — 3b24dcf7+079ff7ea: R0 stateRetired refusal added; generated constructor eliminator index changes.
- `Minidregg.Kernel.ObjectiveActivity.Refusal.liveActivities.elim` — 3b24dcf7+079ff7ea: R0 stateRetired refusal added; generated constructor eliminator index changes.
- `Minidregg.Kernel.ObjectiveActivity.Refusal.memberDenied.elim` — 3b24dcf7+079ff7ea: R0 stateRetired refusal added; generated constructor eliminator index changes.
- `Minidregg.Kernel.ObjectiveActivity.Refusal.memberDomainsFull.elim` — 3b24dcf7+079ff7ea: R0 stateRetired refusal added; generated constructor eliminator index changes.
- `Minidregg.Kernel.ObjectiveActivity.Refusal.memberFrozen.elim` — 3b24dcf7+079ff7ea: R0 stateRetired refusal added; generated constructor eliminator index changes.
- `Minidregg.Kernel.ObjectiveActivity.Refusal.migrationFault.elim` — 3b24dcf7+079ff7ea: R0 stateRetired refusal added; generated constructor eliminator index changes.
- `Minidregg.Kernel.ObjectiveActivity.Refusal.migrationShape.elim` — 3b24dcf7+079ff7ea: R0 stateRetired refusal added; generated constructor eliminator index changes.
- `Minidregg.Kernel.ObjectiveActivity.Refusal.notDraining.elim` — 3b24dcf7+079ff7ea: R0 stateRetired refusal added; generated constructor eliminator index changes.
- `Minidregg.Kernel.ObjectiveActivity.Refusal.notSubtype.elim` — 3b24dcf7+079ff7ea: R0 stateRetired refusal added; generated constructor eliminator index changes.
- `Minidregg.Kernel.ObjectiveActivity.Refusal.notUpgradeAuthority.elim` — 3b24dcf7+079ff7ea: R0 stateRetired refusal added; generated constructor eliminator index changes.
- `Minidregg.Kernel.ObjectiveActivity.Refusal.notYetDeadline.elim` — 3b24dcf7+079ff7ea: R0 stateRetired refusal added; generated constructor eliminator index changes.
- `Minidregg.Kernel.ObjectiveActivity.Refusal.policyLoosened.elim` — 3b24dcf7+079ff7ea: R0 stateRetired refusal added; generated constructor eliminator index changes.
- `Minidregg.Kernel.ObjectiveActivity.Refusal.rebirthDisposition.elim` — 3b24dcf7+079ff7ea: R0 stateRetired refusal added; generated constructor eliminator index changes.
- `Minidregg.Kernel.ObjectiveActivity.Refusal.rebirthTarget.elim` — 3b24dcf7+079ff7ea: R0 stateRetired refusal added; generated constructor eliminator index changes.
- `Minidregg.Kernel.ObjectiveActivity.Refusal.samePin.elim` — 3b24dcf7+079ff7ea: R0 stateRetired refusal added; generated constructor eliminator index changes.
- `Minidregg.Kernel.ObjectiveActivity.Refusal.stateTypeNotData.elim` — 3b24dcf7+079ff7ea: R0 stateRetired refusal added; generated constructor eliminator index changes.
- `Minidregg.Kernel.ObjectiveActivity.Refusal.upgradeUnderWay.elim` — 3b24dcf7+079ff7ea: R0 stateRetired refusal added; generated constructor eliminator index changes.
- `Minidregg.Kernel.ObjectiveActivityGateRoute.derived_route` — de1a3a33: R2 checked commit API: judge returns indexed evidence, writer/replay consume it, and route/source theorems retain conclusions under Judged evidence.
- `Minidregg.Kernel.ObjectiveActivityGateRoute.judge_source` — de1a3a33: R2 checked commit API: judge returns indexed evidence, writer/replay consume it, and route/source theorems retain conclusions under Judged evidence.
- `Minidregg.Kernel.ObjectiveActivityReceiver.callRefusal_encode_roundtrip` — 775240ec+de1a3a33: charged-refusal byte codec: roundtrip now states the live callRefusalStream codec, replacing Encodable Nat encoding; subsequently moved to Core.
- `Minidregg.Kernel.ObjectiveCall.HeldInbox.clean` — 079ff7ea: pole generation inboxes: preserve generation across FIFO steps and use snapshot-selected generation cells with exact generation evidence.
- `Minidregg.Kernel.ObjectiveCall.HeldInbox.lawful` — 079ff7ea: pole generation inboxes: preserve generation across FIFO steps and use snapshot-selected generation cells with exact generation evidence.
- `Minidregg.Kernel.ObjectiveCall.HeldInbox.mk` — 079ff7ea: pole generation inboxes: preserve generation across FIFO steps and use snapshot-selected generation cells with exact generation evidence.
- `Minidregg.Kernel.ObjectiveCall.HeldInbox.readExact` — 079ff7ea: pole generation inboxes: preserve generation across FIFO steps and use snapshot-selected generation cells with exact generation evidence.
- `Minidregg.Kernel.ObjectiveCall.Mail.inboxes_lawful` — 079ff7ea: pole generation inboxes: preserve generation across FIFO steps and use snapshot-selected generation cells with exact generation evidence.
- `Minidregg.Kernel.ObjectiveSend.Mail.inboxes_bounded` — 079ff7ea: pole generation inboxes: preserve generation across FIFO steps and use snapshot-selected generation cells with exact generation evidence.
- `Minidregg.Kernel.ObjectiveSend.MessageDelivery.activityExact` — 079ff7ea: pole generation inboxes: preserve generation across FIFO steps and use snapshot-selected generation cells with exact generation evidence.
- `Minidregg.Kernel.ObjectiveSend.MessageDelivery.batchExact` — 079ff7ea: pole generation inboxes: preserve generation across FIFO steps and use snapshot-selected generation cells with exact generation evidence.
- `Minidregg.Kernel.ObjectiveSend.MessageDelivery.clean` — 079ff7ea: pole generation inboxes: preserve generation across FIFO steps and use snapshot-selected generation cells with exact generation evidence.
- `Minidregg.Kernel.ObjectiveSend.MessageDelivery.debits_only_purse` — 079ff7ea: pole generation inboxes: preserve generation across FIFO steps and use snapshot-selected generation cells with exact generation evidence.
- `Minidregg.Kernel.ObjectiveSend.MessageDelivery.escrow_conserves` — 079ff7ea: pole generation inboxes: preserve generation across FIFO steps and use snapshot-selected generation cells with exact generation evidence.
- `Minidregg.Kernel.ObjectiveSend.MessageDelivery.failed_delivery_posts` — 079ff7ea: pole generation inboxes: preserve generation across FIFO steps and use snapshot-selected generation cells with exact generation evidence.
- `Minidregg.Kernel.ObjectiveSend.MessageDelivery.readExact` — 079ff7ea: pole generation inboxes: preserve generation across FIFO steps and use snapshot-selected generation cells with exact generation evidence.
- `Minidregg.Kernel.ObjectiveSend.escrow_conservation` — 079ff7ea: pole generation inboxes: preserve generation across FIFO steps and use snapshot-selected generation cells with exact generation evidence.
- `Minidregg.Kernel.ObjectiveSend.seedMail` — 079ff7ea: pole generation inboxes: preserve generation across FIFO steps and use snapshot-selected generation cells with exact generation evidence.
- `Minidregg.Kernel.World.Reject.cellPresent.elim` — 8aacd180: R0 absence guards: Turn gains absent, admit_of requires absentCheck = none, and Reject.cellAbsent shifts generated constructor eliminator indices.
- `Minidregg.Kernel.World.Reject.chargeMismatch.elim` — 8aacd180: R0 absence guards: Turn gains absent, admit_of requires absentCheck = none, and Reject.cellAbsent shifts generated constructor eliminator indices.
- `Minidregg.Kernel.World.Reject.duplicateNullifier.elim` — 8aacd180: R0 absence guards: Turn gains absent, admit_of requires absentCheck = none, and Reject.cellAbsent shifts generated constructor eliminator indices.
- `Minidregg.Kernel.World.Reject.guardFailed.elim` — 8aacd180: R0 absence guards: Turn gains absent, admit_of requires absentCheck = none, and Reject.cellAbsent shifts generated constructor eliminator indices.
- `Minidregg.Kernel.World.Reject.imageNotRom.elim` — 8aacd180: R0 absence guards: Turn gains absent, admit_of requires absentCheck = none, and Reject.cellAbsent shifts generated constructor eliminator indices.
- `Minidregg.Kernel.World.Reject.kindMismatch.elim` — 8aacd180: R0 absence guards: Turn gains absent, admit_of requires absentCheck = none, and Reject.cellAbsent shifts generated constructor eliminator indices.
- `Minidregg.Kernel.World.Reject.missingCell.elim` — 8aacd180: R0 absence guards: Turn gains absent, admit_of requires absentCheck = none, and Reject.cellAbsent shifts generated constructor eliminator indices.
- `Minidregg.Kernel.World.Reject.missingParent.elim` — 8aacd180: R0 absence guards: Turn gains absent, admit_of requires absentCheck = none, and Reject.cellAbsent shifts generated constructor eliminator indices.
- `Minidregg.Kernel.World.Reject.noHead.elim` — 8aacd180: R0 absence guards: Turn gains absent, admit_of requires absentCheck = none, and Reject.cellAbsent shifts generated constructor eliminator indices.
- `Minidregg.Kernel.World.Reject.nullifierSpent.elim` — 8aacd180: R0 absence guards: Turn gains absent, admit_of requires absentCheck = none, and Reject.cellAbsent shifts generated constructor eliminator indices.
- `Minidregg.Kernel.World.Reject.outsideWindow.elim` — 8aacd180: R0 absence guards: Turn gains absent, admit_of requires absentCheck = none, and Reject.cellAbsent shifts generated constructor eliminator indices.
- `Minidregg.Kernel.World.Reject.overAllowance.elim` — 8aacd180: R0 absence guards: Turn gains absent, admit_of requires absentCheck = none, and Reject.cellAbsent shifts generated constructor eliminator indices.
- `Minidregg.Kernel.World.Reject.replayedTransaction.elim` — 8aacd180: R0 absence guards: Turn gains absent, admit_of requires absentCheck = none, and Reject.cellAbsent shifts generated constructor eliminator indices.
- `Minidregg.Kernel.World.Reject.retireNonEmpty.elim` — 8aacd180: R0 absence guards: Turn gains absent, admit_of requires absentCheck = none, and Reject.cellAbsent shifts generated constructor eliminator indices.
- `Minidregg.Kernel.World.Reject.retiredIdentifier.elim` — 8aacd180: R0 absence guards: Turn gains absent, admit_of requires absentCheck = none, and Reject.cellAbsent shifts generated constructor eliminator indices.
- `Minidregg.Kernel.World.Turn.mk` — 8aacd180: R0 absence guards: Turn gains absent, admit_of requires absentCheck = none, and Reject.cellAbsent shifts generated constructor eliminator indices.
- `Minidregg.Kernel.World.admit_of` — 8aacd180: R0 absence guards: Turn gains absent, admit_of requires absentCheck = none, and Reject.cellAbsent shifts generated constructor eliminator indices.
- `private Minidregg.Kernel.ObjectiveSend.MessageDelivery.mk @Kernel.ObjectiveSend` — 079ff7ea: pole generation inboxes: preserve generation across FIFO steps and use snapshot-selected generation cells with exact generation evidence.
