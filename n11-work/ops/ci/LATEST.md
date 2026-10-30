# CI latest (run 40973981403)

```
40973981403 completed success 76b6835e 2026-10-29T23:33:47Z
40973934446 completed success ef13cf90 2026-10-29T23:33:22Z
40957920638 completed success a96d4ec1 2026-10-29T21:27:12Z
40949277719 completed success f30e46f0 2026-10-29T20:28:02Z
40935785584 completed success cea391a9 2026-10-29T18:58:28Z
```

## summary.json
```json
{
 "sha": "76b6835e5d6ff2c166cac703a0d55f33dc54303d",
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
   "N11Formalization.Paid16GeneralNext1182",
   "0"
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
   "N11Formalization.EnergyTerminalBatchB13Main",
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
 "built_count": 2,
 "errors_head": [
  "✖ [9300/9300] Building N11Formalization.EnergyTerminalBatchB13 (4.4s)",
  "error: N11Formalization/EnergyTerminalBatchB13.lean:18:3: Unknown constant `Finset.all_eq_true.mp`",
  "error: N11Formalization/EnergyTerminalBatchB13.lean:23:3: Unknown constant `Finset.all_eq_true.mp`",
  "error: Lean exited with code 1",
  "error: build failed",
  "✖ [10617/10624] Building N11Formalization.EnergyTerminalBatchB13 (3.9s)",
  "error: N11Formalization/EnergyTerminalBatchB13.lean:18:3: Unknown constant `Finset.all_eq_true.mp`",
  "error: N11Formalization/EnergyTerminalBatchB13.lean:23:3: Unknown constant `Finset.all_eq_true.mp`",
  "error: Lean exited with code 1",
  "error: build failed",
  "✖ [9260/9260] Building N11Formalization.SevenClassQ0Deg3Cos (4.5s)",
  "error: N11Formalization/SevenClassQ0Deg3Cos.lean:203:6: No goals to be solved",
  "error: Lean exited with code 1",
  "error: build failed",
  "✖ [9261/9261] Building N11Formalization.SevenClassQ0Deg3Bins (4.1s)",
  "error: N11Formalization/SevenClassQ0Deg3Bins.lean:64:47: unsolved goals",
  "error: N11Formalization/SevenClassQ0Deg3Bins.lean:81:55: Application type mismatch: The argument",
  "error: Lean exited with code 1",
  "error: build failed",
  "✖ [9261/9262] Building N11Formalization.SevenClassQ0Deg3Bins (4.0s)",
  "error: N11Formalization/SevenClassQ0Deg3Bins.lean:64:47: unsolved goals",
  "error: N11Formalization/SevenClassQ0Deg3Bins.lean:81:55: Application type mismatch: The argument",
  "error: Lean exited with code 1",
  "error: build failed",
  "✖ [10725/10727] Building N11Formalization.SharedMomentConcreteSwitchBatch (1254s)",
  "error: Lean exited with code 137",
  "error: build failed"
 ]
}```
## build log tail
```
runner/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean /home/runner/work/DiskCoveringProofs/DiskCoveringProofs/n11-work/lean/N11Formalizati
MEM 00:25:13 avail=1890MB top: 13742024 /home/runner/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean /home/runner/work/DiskCoveringProofs/DiskCoveringProofs/n11-work/lean/N11Formalizati
MEM 00:25:33 avail=1547MB top: 13864996 /home/runner/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean /home/runner/work/DiskCoveringProofs/DiskCoveringProofs/n11-work/lean/N11Formalizati
MEM 00:25:53 avail=1350MB top: 13847088 /home/runner/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean /home/runner/work/DiskCoveringProofs/DiskCoveringProofs/n11-work/lean/N11Formalizati
MEM 00:26:13 avail=1118MB top: 14111884 /home/runner/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean /home/runner/work/DiskCoveringProofs/DiskCoveringProofs/n11-work/lean/N11Formalizati
MEM 00:26:33 avail=1033MB top: 14277788 /home/runner/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean /home/runner/work/DiskCoveringProofs/DiskCoveringProofs/n11-work/lean/N11Formalizati
MEM 00:26:53 avail=949MB top: 14501856 /home/runner/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean /home/runner/work/DiskCoveringProofs/DiskCoveringProofs/n11-work/lean/N11Formalizati
MEM 00:27:13 avail=943MB top: 14488712 /home/runner/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean /home/runner/work/DiskCoveringProofs/DiskCoveringProofs/n11-work/lean/N11Formalizati
MEM 00:27:33 avail=937MB top: 14461668 /home/runner/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean /home/runner/work/DiskCoveringProofs/DiskCoveringProofs/n11-work/lean/N11Formalizati
MEM 00:27:53 avail=586MB top: 14761312 /home/runner/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean /home/runner/work/DiskCoveringProofs/DiskCoveringProofs/n11-work/lean/N11Formalizati
OOM-GUARD killing lean (avail=584MB)
✖ [10725/10727] Building N11Formalization.SharedMomentConcreteSwitchBatch (1254s)
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
