# Lane B notes

## 2026-10-29T02:00Z - session part 15: CI shutdown before lane B; source audit

### Done
- Checked run `40797575073` / job `123204085190`: completed **failure**, exit
  `143` at `01:52:31Z` because the runner received a shutdown signal. The log
  contains no Lean `error:` for lane B. It reached only
  `=== BUILD N11Formalization.C450ChainCompletion` (last progress
  `[8936/10257]`), so none of the four B targets received a kernel verdict.
- Downloaded and searched the full 470632-byte job log. This is infra failure,
  not evidence against a B module, and must not be described as a red module.
- Audited generated `Paid16GeneralNext1182.new_count`: all 28 pairwise facts are
  present, the seven assembled union-disjointness facts have the correct
  right-associated types, and card assembly uses one fact per union. B13's
  `paidIDs` is exactly `B12.paidIDs ∪ Next1182.newIDs`; its old/new split
  dispatches B11 and Next505 branches separately. No type or direction error was
  found by source inspection. This is a static audit, **not** elaboration.
- Re-hashed the four source files and `TARGETS.txt`; values recorded below.

### Files (SHA256 of current bytes)
- `n11-work/lean/N11Formalization/Paid16GeneralNext1182.lean`
  `CDCF2B97C4ABB986F8E60DC4AD720C242E2C2B7C2D37BD9A4AD180C9A3145C27`
- `n11-work/lean/N11Formalization/EnergyTerminalBatchB13.lean`
  `54508878D90582A32B7FEF23532FE8892D29D9C30CE002951181979E3F53A75B`
- `n11-work/lean/N11Formalization/EnergyTerminalResidualCensus.lean`
  `4D4124713E50CDF3A3CA602D15737572570CB1447720B940C8B7C6E28E70645B`
- `n11-work/lean/N11Formalization/EnergyTerminalBatchB13Main.lean`
  `2A6A206FE49CD299FCA69221B12B888B55EF6A3A92E34189B3E48C72761D0F98`
- `n11-work/ops/lanes/B/TARGETS.txt`
  `8F8BA4842F17F3BE779A979EB3A69D17B1313D3D2967A017A4DD359D9B74B179`

### Checks executed (scope)
- GitHub Actions metadata and worker log only.
- `rg`/`sed` source audit of hierarchy proofs; `sha256sum` on files above.
- No local project Lean build was started (2-core worker rule); all four B
  targets remain **CI pending**, not paid.

### Still unproved
- Elaboration of all four targets, including 35 Next1182 disjointness facts,
  B13 old/new disjointness and `paid_count = 1997`, the 51 census interval
  facts, literal `residualIDs.card = 389`, and B13Main's transfer theorem.
- `ActualMetricClassReduction.SevenClassExclusions` remains open; B13Main is
  conditional on it and on lane A's `C450ChainCompletionMain`.

### Next concrete step
- Supervisor: place lane B before the long lane-C target in serial CI order (or
  launch a B-only job). Current order has now starved B twice by shutdown. Then
  quote the first B `error:` and patch only that error.
- If B is green, request root import of `EnergyTerminalBatchB13Main`.

## Retained engineering facts
- **ROOT-IMPORT REQUEST (only after CI green):** import
  `EnergyTerminalBatchB13Main` instead of `EnergyTerminalBatchB12Main`.
- Next1182 has 1182 members; pairwise kernel checks compare at most two literal
  chunks, and its hierarchy is assembled by `Finset.disjoint_union_right`.
- Census reconstruction is 2506 terminals - 120 sharp - 1997 paid = 389, with
  literal chunks 100/100/100/89; the old 389 was manifest arithmetic only.
- B11 straddles the 2565 boundary. If CI rejects B13, split B11 into B10 plus
  G03-G12 rather than assuming an interval.
- `Finset.disjoint_left.mp` needs `(a := a)` in these generated proofs.
- Emitters: `emit_next1182_top.py`, `emit_residual_census.py`; the latter exactly
  reproduced the committed census bytes and all count assertions.
- Mathlib-probe attempts gave no verdict (timeouts / incomplete prelude); CI is
  the only Lean-build authority.
