EXPERT (2026-10-30):
- Do not claim energy 1997 until DescentBounds, B13, and B13Main each exit 0.
- `univ.image nodeID` must not be decoded with one-shot `decide +kernel`: it
  traverses Fin 5011 rather than the 21-entry packet vector.
- Current G proof shape is `mem_image` + `fin_cases` + `norm_num [nodeID]`.
- If all three targets are green, ask the supervisor to replace the root
  B12Main import with B13Main; that is when credit 815→1997 and residual 389
  become paid, not before.

# Lane B notes

## Condensed history

- Next1182 (1182 ids, 57 blocks) and Next505Bounds are CI green. The closure is
  B11 310 + Next505 505 + Next1182 1182 = 1997 paid; 2506 terminals, 120 sharp,
  residual 389.
- Earlier B13 revisions failed at nonexistent `Finset.all_eq_true.mp`, then at
  large kernel decodes and broad `simp`/`whnf`. The descent module now splits
  B10/B11/Remaining210 into small image/union layers and a corrected 27-id B09
  high classification.
- Shared frozen-dependency OOMs and the root OOM are not lane-B mathematical
  verdicts. Source/inventory/byte audits are not Lean proof credit.

## Retained engineering facts

- `Finset.card_biUnion` takes disjointness explicitly. Pairwise disjointness of
  `Function.onFun` parts needs `change Disjoint (part i) (part j)` first.
- Part-local Next1182 lower bounds transfer globally through the full
  conjunctive bound plus `omega`.
- `Finset.disjoint_left.mp` may need `(a := a)` when the element is implicit.
- Emitters: `emit_next1182_top.py`, `emit_next505_bounds.py`,
  `emit_residual_census.py`, `emit_b13_descent_bounds.py`. Audits:
  `audit_next1182_blocks.py`, `audit_b13_descent.py`, `audit_b13main.py`.
- **ROOT-IMPORT REQUEST (only after CI green):** import
  `EnergyTerminalBatchB13Main` instead of `EnergyTerminalBatchB12Main`.

## 2026-10-30 - session part 11: lock G decode repair

### Done
- Reloaded GUIDANCE, Lane B notes, LANES, retained `START_HERE.md`, and ran
  `python tools/project_status.py --check` (exit 0; handoff index only).
- Inspected `ops/ci/LATEST.md`; its latest artifact predates source
  `B5C9501F...`, so it cannot verdict the current `norm_num` repair.
- Added a regression check to `audit_b13_descent.py`: exactly twelve G-block
  proofs must use `fin_cases i <;> norm_num [Gxx.nodeID]`. Regenerated the Lean
  module from its Python emitter and reran the source audits.
- Attempted two small local Lean probes (`Mathlib` and `Std` only). Both were
  killed by the 90–120 s bounds under shared-host contention; the probe cache
  has no Mathlib dependency oleans. These are infrastructure failures, not Lean
  elaboration verdicts.

### Files (SHA256, uppercase)
- `EnergyTerminalBatchB13DescentBounds.lean`
  `B5C9501F339817B4A1ABE6AB361B6C690891544F3BFA520D6DD49B48E5858214`.
- `EnergyTerminalBatchB13.lean`
  `3DD37313505E0E8D608D50D42D3AFB1F1E08CEBBDF1ACD5DB570F57D9DC8FD03`.
- `EnergyTerminalBatchB13Main.lean`
  `2A6A206FE49CD299FCA69221B12B888B55EF6A3A92E34189B3E48C72761D0F98`.
- `emit_b13_descent_bounds.py`
  `709FA3FBF1706D0BF1EB191789D7876921AACC0A3BB22E6FF8E5924D1919CBC3`.
- `audit_b13_descent.py`
  `B7416A297487E1DE6AC9E626AB2A87D7626935E69FA5060735D1DD8D723CD2BD`.
- `TARGETS.txt`
  `4E8E73251E43B27E7297C5D6CB21BD04FB93195021A5128C364A09795A476600`.

### Checks (exact scope)
- `audit_b13_descent.py` exit 0: all 19 static checks true, including twelve
  `norm_num` decodes, zero `decide +kernel`, 16 structural image decodes, nine
  B09 layers, 27 high ids, 57 literal blocks / 1182 ids, and exact emitter
  reproduction.
- `audit_b13main.py` exit 0: static imports/API/target membership only.
- `audit_b13_closure.py` exit 0: all 13 manifest inventory checks; counts above.
- `py_compile` exit 0 for the emitter and audit; `git diff --check` exit 0.
- No local Lean build completed. Full kernel elaboration remains CI-only.

### Still unproved / unverified
- `B5C9501F...`, B13 `3DD37313...`, and B13Main `2A6A206F...` are **CI pending /
  unpaid**. Residual 389, SevenClassExclusions, and the arbitrary-center
  full-disk theorem remain unpaid.

### Next concrete step
- On the first CI run binding these hashes, require exit 0 in order
  DescentBounds, B13, B13Main. Use the first module-local error if red. If all
  green, request the documented root import replacement B12Main → B13Main.
