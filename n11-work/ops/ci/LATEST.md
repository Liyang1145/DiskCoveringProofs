# CI latest (run 41001693009)

```
41008974701 in_progress null 43b1d43f 2026-10-30T05:32:14Z
41001693009 completed success e5875cf8 2026-10-30T04:13:30Z
41000327612 completed cancelled 13e6affb 2026-10-30T03:59:03Z
40998371772 completed success 88918335 2026-10-30T03:36:58Z
40988698121 completed success 2fdf1a1c 2026-10-30T01:55:46Z
```

## summary.json
```json
{
 "sha": "e5875cf83c231e8a14a0bf154107057b3cfae944",
 "exits": [
  [
   "N11Formalization.FrozenCapRationalCore",
   "0"
  ],
  [
   "N11Formalization.PaidCellCertificateM",
   "0"
  ],
  [
   "N11Formalization.PaidCellCertificateMCap",
   "0"
  ],
  [
   "N11Formalization.FrozenCapWideFieldWitnesses",
   "0"
  ],
  [
   "N11Formalization.FrozenCapWideFieldRowCaps",
   "1"
  ],
  [
   "N11Formalization.Paid16GeneralNext1182",
   "0"
  ],
  [
   "N11Formalization.EnergyTerminalBatchB13Next505Bounds",
   "0"
  ],
  [
   "N11Formalization.EnergyTerminalBatchB13DescentBounds",
   "1"
  ],
  [
   "N11Formalization.EnergyTerminalBatchB13",
   "1"
  ],
  [
   "N11Formalization.EnergyTerminalBatchB13Main",
   "1"
  ],
  [
   "N11Formalization.C450ChainCompletionMain",
   "0"
  ],
  [
   "N11Formalization.SevenClassQ0Deg3Cos",
   "0"
  ],
  [
   "N11Formalization.SevenClassQ0Deg3Mono",
   "0"
  ],
  [
   "N11Formalization.SevenClassQ0Deg3Bins",
   "1"
  ],
  [
   "N11Formalization.SevenClassQ0Deg3EndpointChecks",
   "1"
  ],
  [
   "N11Formalization",
   "1"
  ]
 ],
 "built_count": 1,
 "errors_head": [
  "✖ [9139/9139] Building N11Formalization.FrozenCapWideFieldRowCaps (84s)",
  "error: N11Formalization/FrozenCapWideFieldRowCaps.lean:31:0: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached",
  "error: N11Formalization/FrozenCapWideFieldRowCaps.lean:52:0: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached",
  "error: N11Formalization/FrozenCapWideFieldRowCaps.lean:73:0: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached",
  "error: N11Formalization/FrozenCapWideFieldRowCaps.lean:94:0: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached",
  "error: N11Formalization/FrozenCapWideFieldRowCaps.lean:115:0: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached",
  "error: N11Formalization/FrozenCapWideFieldRowCaps.lean:136:0: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached",
  "error: N11Formalization/FrozenCapWideFieldRowCaps.lean:157:0: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached",
  "error: Lean exited with code 1",
  "error: build failed",
  "✖ [9204/9204] Building N11Formalization.EnergyTerminalBatchB13DescentBounds (24s)",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:242:43: Unknown identifier `EnergyTerminalBatchB11.paidIDs`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:244:6: Unknown identifier `EnergyTerminalBatchB11.paidIDs`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:243:37: unsolved goals",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:251:8: Unknown identifier `Paid16GeneralNext1182.newIDs`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:254:8: Unknown identifier `Paid16GeneralNext1182.new_mem`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:272:8: Unknown identifier `Paid16GeneralNext1182.new_mem`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:290:8: Unknown identifier `Paid16GeneralNext1182.new_mem`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:308:8: Unknown identifier `Paid16GeneralNext1182.new_mem`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:326:8: Unknown identifier `Paid16GeneralNext1182.new_mem`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:344:8: Unknown identifier `Paid16GeneralNext1182.new_mem`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:362:8: Unknown identifier `Paid16GeneralNext1182.new_mem`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:380:8: Unknown identifier `Paid16GeneralNext1182.new_mem`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:398:8: Unknown identifier `Paid16GeneralNext1182.new_mem`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:416:8: Unknown identifier `Paid16GeneralNext1182.new_mem`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:434:8: Unknown identifier `Paid16GeneralNext1182.new_mem`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:452:8: Unknown identifier `Paid16GeneralNext1182.new_mem`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:470:8: Unknown identifier `Paid16GeneralNext1182.new_mem`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:488:8: Unknown identifier `Paid16GeneralNext1182.new_mem`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:506:8: Unknown identifier `Paid16GeneralNext1182.new_mem`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:524:8: Unknown identifier `Paid16GeneralNext1182.new_mem`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:542:8: Unknown identifier `Paid16GeneralNext1182.new_mem`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:560:8: Unknown identifier `Paid16GeneralNext1182.new_mem`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:578:8: Unknown identifier `Paid16GeneralNext1182.new_mem`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:596:8: Unknown identifier `Paid16GeneralNext1182.new_mem`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:614:8: Unknown identifier `Paid16GeneralNext1182.new_mem`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:632:8: Unknown identifier `Paid16GeneralNext1182.new_mem`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:650:8: Unknown identifier `Paid16GeneralNext1182.new_mem`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:668:8: Unknown identifier `Paid16GeneralNext1182.new_mem`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:686:8: Unknown identifier `Paid16GeneralNext1182.new_mem`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:704:8: Unknown identifier `Paid16GeneralNext1182.new_mem`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:722:8: Unknown identifier `Paid16GeneralNext1182.new_mem`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:744:8: Unknown identifier `N11Formalization.EnergyTerminalBatchB13DescentBounds.b11_bound`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:747:14: Unknown constant `N11Formalization.EnergyTerminalBatchB13DescentBounds.b11_bound`",
  "error: Lean exited with code 1",
  "error: build failed",
  "✖ [9300/9301] Building N11Formalization.EnergyTerminalBatchB13DescentBounds (24s)",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:242:43: Unknown identifier `EnergyTerminalBatchB11.paidIDs`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:244:6: Unknown identifier `EnergyTerminalBatchB11.paidIDs`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:243:37: unsolved goals",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:251:8: Unknown identifier `Paid16GeneralNext1182.newIDs`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:254:8: Unknown identifier `Paid16GeneralNext1182.new_mem`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:272:8: Unknown identifier `Paid16GeneralNext1182.new_mem`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:290:8: Unknown identifier `Paid16GeneralNext1182.new_mem`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:308:8: Unknown identifier `Paid16GeneralNext1182.new_mem`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:326:8: Unknown identifier `Paid16GeneralNext1182.new_mem`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:344:8: Unknown identifier `Paid16GeneralNext1182.new_mem`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:362:8: Unknown identifier `Paid16GeneralNext1182.new_mem`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:380:8: Unknown identifier `Paid16GeneralNext1182.new_mem`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:398:8: Unknown identifier `Paid16GeneralNext1182.new_mem`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:416:8: Unknown identifier `Paid16GeneralNext1182.new_mem`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:434:8: Unknown identifier `Paid16GeneralNext1182.new_mem`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:452:8: Unknown identifier `Paid16GeneralNext1182.new_mem`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:470:8: Unknown identifier `Paid16GeneralNext1182.new_mem`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:488:8: Unknown identifier `Paid16GeneralNext1182.new_mem`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:506:8: Unknown identifier `Paid16GeneralNext1182.new_mem`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:524:8: Unknown identifier `Paid16GeneralNext1182.new_mem`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:542:8: Unknown identifier `Paid16GeneralNext1182.new_mem`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:560:8: Unknown identifier `Paid16GeneralNext1182.new_mem`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:578:8: Unknown identifier `Paid16GeneralNext1182.new_mem`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:596:8: Unknown identifier `Paid16GeneralNext1182.new_mem`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:614:8: Unknown identifier `Paid16GeneralNext1182.new_mem`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:632:8: Unknown identifier `Paid16GeneralNext1182.new_mem`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:650:8: Unknown identifier `Paid16GeneralNext1182.new_mem`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:668:8: Unknown identifier `Paid16GeneralNext1182.new_mem`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:686:8: Unknown identifier `Paid16GeneralNext1182.new_mem`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:704:8: Unknown identifier `Paid16GeneralNext1182.new_mem`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:722:8: Unknown identifier `Paid16GeneralNext1182.new_mem`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:744:8: Unknown identifier `N11Formalization.EnergyTerminalBatchB13DescentBounds.b11_bound`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:747:14: Unknown constant `N11Formalization.EnergyTerminalBatchB13DescentBounds.b11_bound`",
  "error: Lean exited with code 1",
  "error: build failed",
  "✖ [10617/10625] Building N11Formalization.EnergyTerminalBatchB13DescentBounds (24s)",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:242:43: Unknown identifier `EnergyTerminalBatchB11.paidIDs`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:244:6: Unknown identifier `EnergyTerminalBatchB11.paidIDs`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:243:37: unsolved goals",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:251:8: Unknown identifier `Paid16GeneralNext1182.newIDs`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:254:8: Unknown identifier `Paid16GeneralNext1182.new_mem`",
  "error: N11Formalization/EnergyTerminalBatchB13DescentBounds.lean:272:8: Unknown identifier `Paid16GeneralNext1182.new_mem`",
  "error: N11Fo```
## build log tail
```
me/runner/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean /home/runner/work/DiskCoveringProofs/DiskCoveringProofs/n11-work/lean/N11Formalizati
MEM 05:12:33 avail=1239MB top: 13927928 /home/runner/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean /home/runner/work/DiskCoveringProofs/DiskCoveringProofs/n11-work/lean/N11Formalizati
MEM 05:12:54 avail=983MB top: 13995028 /home/runner/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean /home/runner/work/DiskCoveringProofs/DiskCoveringProofs/n11-work/lean/N11Formalizati
MEM 05:13:14 avail=1014MB top: 14117512 /home/runner/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean /home/runner/work/DiskCoveringProofs/DiskCoveringProofs/n11-work/lean/N11Formalizati
MEM 05:13:34 avail=917MB top: 14367380 /home/runner/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean /home/runner/work/DiskCoveringProofs/DiskCoveringProofs/n11-work/lean/N11Formalizati
MEM 05:13:54 avail=976MB top: 14513656 /home/runner/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean /home/runner/work/DiskCoveringProofs/DiskCoveringProofs/n11-work/lean/N11Formalizati
MEM 05:14:14 avail=965MB top: 14484540 /home/runner/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean /home/runner/work/DiskCoveringProofs/DiskCoveringProofs/n11-work/lean/N11Formalizati
MEM 05:14:34 avail=982MB top: 14485436 /home/runner/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean /home/runner/work/DiskCoveringProofs/DiskCoveringProofs/n11-work/lean/N11Formalizati
MEM 05:14:54 avail=895MB top: 14512036 /home/runner/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean /home/runner/work/DiskCoveringProofs/DiskCoveringProofs/n11-work/lean/N11Formalizati
MEM 05:15:14 avail=883MB top: 14423888 /home/runner/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean /home/runner/work/DiskCoveringProofs/DiskCoveringProofs/n11-work/lean/N11Formalizati
OOM-GUARD killing lean (avail=880MB)
✖ [10725/10727] Building N11Formalization.SharedMomentConcreteSwitchBatch (1873s)
trace: .> LEAN_PATH=/home/runner/work/DiskCoveringProofs/DiskCoveringProofs/n11-work/lean/.lake/packages/Cli/.lake/build/lib/lean:/home/runner/work/DiskCoveringProofs/DiskCoveringProofs/n11-work/lean/.lake/packages/batteries/.lake/build/lib/lean:/home/runner/work/DiskCoveringProofs/DiskCoveringProofs/n11-work/lean/.lake/packages/Qq/.lake/build/lib/lean:/home/runner/work/DiskCoveringProofs/DiskCoveringProofs/n11-work/lean/.lake/packages/aesop/.lake/build/lib/lean:/home/runner/work/DiskCoveringProofs/DiskCoveringProofs/n11-work/lean/.lake/packages/proofwidgets/.lake/build/lib/lean:/home/runner/work/DiskCoveringProofs/DiskCoveringProofs/n11-work/lean/.lake/packages/importGraph/.lake/build/lib/lean:/home/runner/work/DiskCoveringProofs/DiskCoveringProofs/n11-work/lean/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/home/runner/work/DiskCoveringProofs/DiskCoveringProofs/n11-work/lean/.lake/packages/plausible/.lake/build/lib/lean:/home/runner/work/DiskCoveringProofs/DiskCoveringProofs/n11-work/lean/.lake/packages/mathlib/.lake/build/lib/lean:/home/runner/work/DiskCoveringProofs/DiskCoveringProofs/n11-work/lean/.lake/build/lib/lean /home/runner/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean /home/runner/work/DiskCoveringProofs/DiskCoveringProofs/n11-work/lean/N11Formalization/SharedMomentConcreteSwitchBatch.lean -o /home/runner/work/DiskCoveringProofs/DiskCoveringProofs/n11-work/lean/.lake/build/lib/lean/N11Formalization/SharedMomentConcreteSwitchBatch.olean -i /home/runner/work/DiskCoveringProofs/DiskCoveringProofs/n11-work/lean/.lake/build/lib/lean/N11Formalization/SharedMomentConcreteSwitchBatch.ilean -c /home/runner/work/DiskCoveringProofs/DiskCoveringProofs/n11-work/lean/.lake/build/ir/N11Formalization/SharedMomentConcreteSwitchBatch.c --setup /home/runner/work/DiskCoveringProofs/DiskCoveringProofs/n11-work/lean/.lake/build/ir/N11Formalization/SharedMomentConcreteSwitchBatch.setup.json --json
info: N11Formalization/SharedMomentConcreteSwitchBatch.lean:3853:0: 'N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch0_full_angle_upper' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: N11Formalization/SharedMomentConcreteSwitchBatch.lean:3854:0: 'N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch0_node_762' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: N11Formalization/SharedMomentConcreteSwitchBatch.lean:7685:0: 'N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch1_full_angle_upper' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: N11Formalization/SharedMomentConcreteSwitchBatch.lean:7686:0: 'N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch1_node_760' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: N11Formalization/SharedMomentConcreteSwitchBatch.lean:12277:0: 'N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch2_full_angle_upper' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: N11Formalization/SharedMomentConcreteSwitchBatch.lean:12278:0: 'N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch2_node_912' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: N11Formalization/SharedMomentConcreteSwitchBatch.lean:16579:0: 'N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch3_full_angle_upper' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: N11Formalization/SharedMomentConcreteSwitchBatch.lean:16580:0: 'N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch3_node_854' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: N11Formalization/SharedMomentConcreteSwitchBatch.lean:21321:0: 'N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch4_full_angle_upper' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: stdout:
{"cap

error: Lean exited with code 137
Some required targets logged failures:
- N11Formalization.SharedMomentConcreteSwitchBatch
error: build failed
=== EXIT N11Formalization 1
```
