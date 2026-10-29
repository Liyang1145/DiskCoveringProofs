# CI latest (run 40861839784)

```
40861839784 completed success 1a7c95c3 2026-10-29T10:59:20Z
40857762507 completed success 0cb4f8de 2026-10-29T10:27:52Z
40818062141 completed success a201da0d 2026-10-29T04:29:49Z
40816724351 completed cancelled d08278f0 2026-10-29T04:15:28Z
40815681024 completed success 1d7515cb 2026-10-29T04:04:38Z
```

## summary.json
```json
{
 "sha": "1a7c95c3aebe3a623cb8492593884fde77143274",
 "exits": [
  [
   "N11Formalization.FrozenCapRationalCore",
   "0"
  ],
  [
   "N11Formalization.PaidCellCertificateM",
   "1"
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
   "N11Formalization.EnergyTerminalBatchB13",
   "1"
  ],
  [
   "N11Formalization.C450Source36Segment",
   "0"
  ],
  [
   "N11Formalization.C450ChainCompletionEndpoint",
   "0"
  ],
  [
   "N11Formalization.C450ChainCompletionTail",
   "0"
  ],
  [
   "N11Formalization.C450ChainCompletionMid1",
   "0"
  ],
  [
   "N11Formalization.C450ChainCompletionMid2",
   "0"
  ],
  [
   "N11Formalization.C450ChainCompletionMid3",
   "0"
  ],
  [
   "N11Formalization.C450ChainCompletion",
   "0"
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
   "N11Formalization.SevenClassQ0Deg3UpperReduction",
   "1"
  ],
  [
   "N11Formalization.SevenClassQ0Deg3UpperReductionCounterexample",
   "1"
  ],
  [
   "N11Formalization.SevenClassQ0Deg3UpperReductionUnimodal",
   "1"
  ],
  [
   "N11Formalization.SevenClassQ0Deg3EdgeReal",
   "1"
  ],
  [
   "N11Formalization.SevenClassQ0Deg3EdgeSuffixHigh",
   "1"
  ],
  [
   "N11Formalization",
   "1"
  ]
 ],
 "built_count": 4,
 "errors_head": [
  "✖ [9153/9153] Building N11Formalization.PaidCellCertificateM (8.6s)",
  "error: N11Formalization/PaidCellCertificateM.lean:69:4: Type mismatch: After simplification, term",
  "error: N11Formalization/PaidCellCertificateM.lean:71:4: Type mismatch: After simplification, term",
  "error: Lean exited with code 1",
  "error: build failed",
  "✖ [9153/9154] Building N11Formalization.PaidCellCertificateM (4.3s)",
  "error: N11Formalization/PaidCellCertificateM.lean:69:4: Type mismatch: After simplification, term",
  "error: N11Formalization/PaidCellCertificateM.lean:71:4: Type mismatch: After simplification, term",
  "error: Lean exited with code 1",
  "error: build failed",
  "✖ [9298/9298] Building N11Formalization.Paid16GeneralNext1182 (39s)",
  "error: N11Formalization/Paid16GeneralNext1182.lean:47:4: (deterministic) timeout at `«tactic execution»`, maximum number of heartbeats (200000) has been reached",
  "error: N11Formalization/Paid16GeneralNext1182.lean:44:0: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached",
  "error: Lean exited with code 1",
  "error: build failed",
  "✖ [9298/9299] Building N11Formalization.Paid16GeneralNext1182 (40s)",
  "error: N11Formalization/Paid16GeneralNext1182.lean:47:4: (deterministic) timeout at `«tactic execution»`, maximum number of heartbeats (200000) has been reached",
  "error: N11Formalization/Paid16GeneralNext1182.lean:44:0: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached",
  "error: Lean exited with code 1",
  "error: build failed",
  "✖ [9260/9260] Building N11Formalization.SevenClassQ0Deg3Cos (4.5s)",
  "error: N11Formalization/SevenClassQ0Deg3Cos.lean:38:47: unsolved goals",
  "error: N11Formalization/SevenClassQ0Deg3Cos.lean:143:8: maximum recursion depth has been reached",
  "error: N11Formalization/SevenClassQ0Deg3Cos.lean:158:12: Tactic `rewrite` failed: motive is not type correct:",
  "error: N11Formalization/SevenClassQ0Deg3Cos.lean:172:2: Type mismatch: After simplification, term",
  "error: Lean exited with code 1",
  "error: build failed",
  "✖ [9260/9264] Building N11Formalization.SevenClassQ0Deg3Mono (3.6s)",
  "error: N11Formalization/SevenClassQ0Deg3Mono.lean:54:53: linarith failed to find a contradiction",
  "error: N11Formalization/SevenClassQ0Deg3Mono.lean:66:9: typeclass instance problem is stuck",
  "error: N11Formalization/SevenClassQ0Deg3Mono.lean:78:4: Unknown identifier `capQ`",
  "error: N11Formalization/SevenClassQ0Deg3Mono.lean:78:14: Unknown identifier `capQ`",
  "error: N11Formalization/SevenClassQ0Deg3Mono.lean:79:9: Unknown identifier `capQ`",
  "error: Lean exited with code 1",
  "error: build failed",
  "✖ [9260/9265] Building N11Formalization.SevenClassQ0Deg3Mono (3.7s)",
  "error: N11Formalization/SevenClassQ0Deg3Mono.lean:54:53: linarith failed to find a contradiction",
  "error: N11Formalization/SevenClassQ0Deg3Mono.lean:66:9: typeclass instance problem is stuck",
  "error: N11Formalization/SevenClassQ0Deg3Mono.lean:78:4: Unknown identifier `capQ`",
  "error: N11Formalization/SevenClassQ0Deg3Mono.lean:78:14: Unknown identifier `capQ`",
  "error: N11Formalization/SevenClassQ0Deg3Mono.lean:79:9: Unknown identifier `capQ`",
  "error: Lean exited with code 1",
  "error: build failed",
  "✖ [9260/9264] Building N11Formalization.SevenClassQ0Deg3Mono (3.6s)",
  "error: N11Formalization/SevenClassQ0Deg3Mono.lean:54:53: linarith failed to find a contradiction",
  "error: N11Formalization/SevenClassQ0Deg3Mono.lean:66:9: typeclass instance problem is stuck",
  "error: N11Formalization/SevenClassQ0Deg3Mono.lean:78:4: Unknown identifier `capQ`",
  "error: N11Formalization/SevenClassQ0Deg3Mono.lean:78:14: Unknown identifier `capQ`",
  "error: N11Formalization/SevenClassQ0Deg3Mono.lean:79:9: Unknown identifier `capQ`",
  "error: Lean exited with code 1",
  "error: build failed",
  "✖ [9260/9266] Building N11Formalization.SevenClassQ0Deg3Mono (4.0s)",
  "error: N11Formalization/SevenClassQ0Deg3Mono.lean:54:53: linarith failed to find a contradiction",
  "error: N11Formalization/SevenClassQ0Deg3Mono.lean:66:9: typeclass instance problem is stuck",
  "error: N11Formalization/SevenClassQ0Deg3Mono.lean:78:4: Unknown identifier `capQ`",
  "error: N11Formalization/SevenClassQ0Deg3Mono.lean:78:14: Unknown identifier `capQ`",
  "error: N11Formalization/SevenClassQ0Deg3Mono.lean:79:9: Unknown identifier `capQ`",
  "error: Lean exited with code 1",
  "✖ [9265/9266] Building N11Formalization.SevenClassQ0Deg3Cos (4.7s)",
  "error: N11Formalization/SevenClassQ0Deg3Cos.lean:38:47: unsolved goals",
  "error: N11Formalization/SevenClassQ0Deg3Cos.lean:143:8: maximum recursion depth has been reached",
  "error: N11Formalization/SevenClassQ0Deg3Cos.lean:158:12: Tactic `rewrite` failed: motive is not type correct:",
  "error: N11Formalization/SevenClassQ0Deg3Cos.lean:172:2: Type mismatch: After simplification, term",
  "error: Lean exited with code 1",
  "error: build failed",
  "✖ [9260/9267] Building N11Formalization.SevenClassQ0Deg3Mono (3.0s)",
  "error: N11Formalization/SevenClassQ0Deg3Mono.lean:54:53: linarith failed to find a contradiction",
  "error: N11Formalization/SevenClassQ0Deg3Mono.lean:66:9: typeclass instance problem is stuck",
  "error: N11Formalization/SevenClassQ0Deg3Mono.lean:78:4: Unknown identifier `capQ`",
  "error: N11Formalization/SevenClassQ0Deg3Mono.lean:78:14: Unknown identifier `capQ`",
  "error: N11Formalization/SevenClassQ0Deg3Mono.lean:79:9: Unknown identifier `capQ`",
  "error: Lean exited with code 1",
  "✖ [9265/9267] Building N11Formalization.SevenClassQ0Deg3Cos (4.5s)",
  "error: N11Formalization/SevenClassQ0Deg3Cos.lean:38:47: unsolved goals",
  "error: N11Formalization/SevenClassQ0Deg3Cos.lean:143:8: maximum recursion depth has been reached",
  "error: N11Formalization/SevenClassQ0Deg3Cos.lean:158:12: Tactic `rewrite` failed: motive is not type correct:",
  "error: N11Formalization/SevenClassQ0Deg3Cos.lean:172:2: Type mismatch: After simplification, term",
  "error: Lean exited with code 1",
  "error: build failed",
  "✖ [10725/10727] Building N11Formalization.SharedMomentConcreteSwitchBatch (1351s)",
  "error: Lean exited with code 137",
  "error: build failed"
 ]
}```
## build log tail
```
ner/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean /home/runner/work/DiskCoveringProofs/DiskCoveringProofs/n11-work/lean/N11Formalizati
MEM 11:42:07 avail=2950MB top: 13642912 /home/runner/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean /home/runner/work/DiskCoveringProofs/DiskCoveringProofs/n11-work/lean/N11Formalizati
MEM 11:42:27 avail=2591MB top: 13958496 /home/runner/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean /home/runner/work/DiskCoveringProofs/DiskCoveringProofs/n11-work/lean/N11Formalizati
MEM 11:42:47 avail=2463MB top: 13974320 /home/runner/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean /home/runner/work/DiskCoveringProofs/DiskCoveringProofs/n11-work/lean/N11Formalizati
MEM 11:43:07 avail=2461MB top: 13969600 /home/runner/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean /home/runner/work/DiskCoveringProofs/DiskCoveringProofs/n11-work/lean/N11Formalizati
MEM 11:43:27 avail=2386MB top: 14003872 /home/runner/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean /home/runner/work/DiskCoveringProofs/DiskCoveringProofs/n11-work/lean/N11Formalizati
MEM 11:43:47 avail=1998MB top: 14021400 /home/runner/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean /home/runner/work/DiskCoveringProofs/DiskCoveringProofs/n11-work/lean/N11Formalizati
MEM 11:44:08 avail=1573MB top: 13980600 /home/runner/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean /home/runner/work/DiskCoveringProofs/DiskCoveringProofs/n11-work/lean/N11Formalizati
MEM 11:44:28 avail=1171MB top: 14034192 /home/runner/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean /home/runner/work/DiskCoveringProofs/DiskCoveringProofs/n11-work/lean/N11Formalizati
MEM 11:44:48 avail=870MB top: 14105940 /home/runner/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean /home/runner/work/DiskCoveringProofs/DiskCoveringProofs/n11-work/lean/N11Formalizati
OOM-GUARD killing lean (avail=878MB)
✖ [10725/10727] Building N11Formalization.SharedMomentConcreteSwitchBatch (1351s)
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
