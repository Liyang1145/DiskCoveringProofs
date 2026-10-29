# CI latest (run 40935785584)

```
40949277719 in_progress null f30e46f0 2026-10-29T20:28:02Z
40935785584 completed success cea391a9 2026-10-29T18:58:28Z
40914236268 completed success 95df31a3 2026-10-29T16:42:38Z
40911502022 completed success e1683b29 2026-10-29T16:25:55Z
40901508838 completed success 1b0171c4 2026-10-29T15:26:02Z
```

## summary.json
```json
{
 "sha": "cea391a9a3f276cfb3c9fde6de3d04cdb69e138d",
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
   "1"
  ],
  [
   "N11Formalization.Paid16GeneralNext1182",
   "1"
  ],
  [
   "N11Formalization.EnergyTerminalBatchB13Next505Bounds",
   "0"
  ],
  [
   "N11Formalization.EnergyTerminalBatchB13",
   "1"
  ],
  [
   "N11Formalization.C450ChainCompletionMain",
   "0"
  ],
  [
   "N11Formalization.SevenClassQ0Deg3Cos",
   "1"
  ],
  [
   "N11Formalization.SevenClassQ0Deg3Mono",
   "0"
  ],
  [
   "N11Formalization",
   "1"
  ]
 ],
 "built_count": 2,
 "errors_head": [
  "✖ [9154/9154] Building N11Formalization.PaidCellCertificateMCap (18s)",
  "error: N11Formalization/PaidCellCertificateMCap.lean:79:6: Type mismatch",
  "error: Lean exited with code 1",
  "error: build failed",
  "✖ [9298/9298] Building N11Formalization.Paid16GeneralNext1182 (19s)",
  "error: N11Formalization/Paid16GeneralNext1182.lean:582:4: Type mismatch",
  "error: N11Formalization/Paid16GeneralNext1182.lean:583:4: Type mismatch",
  "error: N11Formalization/Paid16GeneralNext1182.lean:584:4: Type mismatch",
  "error: N11Formalization/Paid16GeneralNext1182.lean:585:4: Type mismatch",
  "error: N11Formalization/Paid16GeneralNext1182.lean:586:4: Type mismatch",
  "error: N11Formalization/Paid16GeneralNext1182.lean:587:4: Type mismatch",
  "error: N11Formalization/Paid16GeneralNext1182.lean:588:4: Type mismatch",
  "error: N11Formalization/Paid16GeneralNext1182.lean:590:75: unsolved goals",
  "error: Lean exited with code 1",
  "error: build failed",
  "✖ [9299/9300] Building N11Formalization.Paid16GeneralNext1182 (17s)",
  "error: N11Formalization/Paid16GeneralNext1182.lean:582:4: Type mismatch",
  "error: N11Formalization/Paid16GeneralNext1182.lean:583:4: Type mismatch",
  "error: N11Formalization/Paid16GeneralNext1182.lean:584:4: Type mismatch",
  "error: N11Formalization/Paid16GeneralNext1182.lean:585:4: Type mismatch",
  "error: N11Formalization/Paid16GeneralNext1182.lean:586:4: Type mismatch",
  "error: N11Formalization/Paid16GeneralNext1182.lean:587:4: Type mismatch",
  "error: N11Formalization/Paid16GeneralNext1182.lean:588:4: Type mismatch",
  "error: N11Formalization/Paid16GeneralNext1182.lean:590:75: unsolved goals",
  "error: Lean exited with code 1",
  "error: build failed",
  "✖ [9260/9260] Building N11Formalization.SevenClassQ0Deg3Cos (3.6s)",
  "error: N11Formalization/SevenClassQ0Deg3Cos.lean:134:6: Tactic `rewrite` failed: Did not find an occurrence of the pattern",
  "error: N11Formalization/SevenClassQ0Deg3Cos.lean:196:6: No goals to be solved",
  "error: Lean exited with code 1",
  "error: build failed",
  "✖ [10725/10727] Building N11Formalization.SharedMomentConcreteSwitchBatch (963s)",
  "error: Lean exited with code 137",
  "error: build failed"
 ]
}```
## build log tail
```
/runner/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean /home/runner/work/DiskCoveringProofs/DiskCoveringProofs/n11-work/lean/N11Formalizati
MEM 19:18:44 avail=2213MB top: 13804648 /home/runner/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean /home/runner/work/DiskCoveringProofs/DiskCoveringProofs/n11-work/lean/N11Formalizati
MEM 19:19:04 avail=2184MB top: 13737824 /home/runner/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean /home/runner/work/DiskCoveringProofs/DiskCoveringProofs/n11-work/lean/N11Formalizati
MEM 19:19:24 avail=1857MB top: 13963668 /home/runner/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean /home/runner/work/DiskCoveringProofs/DiskCoveringProofs/n11-work/lean/N11Formalizati
MEM 19:19:44 avail=1530MB top: 14045280 /home/runner/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean /home/runner/work/DiskCoveringProofs/DiskCoveringProofs/n11-work/lean/N11Formalizati
MEM 19:20:04 avail=1193MB top: 14169424 /home/runner/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean /home/runner/work/DiskCoveringProofs/DiskCoveringProofs/n11-work/lean/N11Formalizati
MEM 19:20:24 avail=979MB top: 14354824 /home/runner/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean /home/runner/work/DiskCoveringProofs/DiskCoveringProofs/n11-work/lean/N11Formalizati
MEM 19:20:44 avail=940MB top: 14530032 /home/runner/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean /home/runner/work/DiskCoveringProofs/DiskCoveringProofs/n11-work/lean/N11Formalizati
MEM 19:21:04 avail=947MB top: 14524564 /home/runner/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean /home/runner/work/DiskCoveringProofs/DiskCoveringProofs/n11-work/lean/N11Formalizati
MEM 19:21:24 avail=748MB top: 14651716 /home/runner/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean /home/runner/work/DiskCoveringProofs/DiskCoveringProofs/n11-work/lean/N11Formalizati
OOM-GUARD killing lean (avail=747MB)
✖ [10725/10727] Building N11Formalization.SharedMomentConcreteSwitchBatch (963s)
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
