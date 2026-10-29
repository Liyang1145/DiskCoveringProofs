SUPERVISOR (2026-10-29): TARGETS trimmed to Next1182 + B13 until both are
CI-green. B13Main and ResidualCensus stay out until then. Do real work; do not
poll Actions. EXPERT: conditional B13 transfer is sound; do not change paid
count before B13Main is green; remove `maxRecDepth 10000`; aggregate 1182 via
`Finset.univ.biUnion`; split the residual census into 4 chunks + assembly.
No census payment claim before equality and 389-cardinality are kernel-built.

# Lane B notes

## 2026-10-29 - session part 24: explicit card_biUnion hypothesis

### Done
- Found the exact Mathlib signature: `Finset.card_biUnion {t} (h :
  (s : Set ι).PairwiseDisjoint t) : #(s.biUnion t) = ∑ u ∈ s, #(t u)`.
  The prior emitted `rw [newIDs, Finset.card_biUnion]` left the disjointness
  hypothesis as a side goal, making the two-bullet proof depend on rw's goal
  ordering.
- Changed `emit_next1182_top.py` to prove `hdisj` explicitly and rewrite with
  `Finset.card_biUnion hdisj`. `new_count` now has one deterministic rewrite
  goal followed by the eight count facts and a small `decide +kernel`.
- Regenerated `Paid16GeneralNext1182.lean`; inventory is still 1182 and the
  top aggregate source has no `maxRecDepth`.

### Files (SHA256)
- `n11-work/lean/N11Formalization/Paid16GeneralNext1182.lean`
  `87F97BD05360486558B4DD831235F4207440BD099F2DCF4DD6CDCFAD46B3DD50`
- `n11-work/ops/lanes/B/emit_next1182_top.py`
  `E0FEA2E601F2FBB046E2736F367FA6E3CC043542E8B6979159918829C313ECA1`
- `n11-work/ops/lanes/B/emit_next1182_top-report.json`
  `B5E673881A94FA7A90AB2C5D5EAE19F3D0E4C025A8EA3AC34AD021E83F84A5C1`
- `n11-work/lean/N11Formalization/EnergyTerminalBatchB13.lean` (unchanged)
  `00E7AE988BBAD89D1921200602DAB0CD9D68BE8AE2C145B480E7A27BE9A8E79F`
- `n11-work/ops/lanes/B/TARGETS.txt` (unchanged)
  `D0572BD0309F49830EFE59C36F208F624FCEAD21D75974E8CE29D85CC45B7C72`

### Checks executed (scope)
- `python tools/project_status.py --check`: PASSED, handoff index only.
- Emitter rerun: deterministic bytes, manifest inventory assertions passed;
  output is 5604 bytes. Mathlib source confirms the `card_biUnion` signature.
- Forbidden-token scan over both TARGETS and `git diff --check`: clean.
- `lake env lean BiUnionProbe.lean` timed out at 110 s with no output; no
  project build was started. Therefore no Lean verdict for this edit.

### Still unproved / unverified
- `Paid16GeneralNext1182` and B13 remain **CI pending**, not paid. In
  particular the regenerated `hdisj` proof, B13's 1997 count, and radius
  transfer have no kernel verdict.
- The 389 census equality/cardinality, `SevenClassExclusions`, and lane A's
  C450 completion remain open. B13Main is conditional.

### Next concrete step
- On CI, quote the first genuine `error:` for Next1182 and patch only that.
  If green, inspect B13. Separately, split the census into four chunk modules
  with an assembly module while preserving the existing API used by B13Main.

## Earlier progress (condensed)
- Sessions 21-22 replaced B13's eight large old/new kernel decodes with one
  B11 bound plus eight `omega` contradictions.
- Session 18 proved the prior red logs were frozen-dependency OOM kills
  (`DBMSourceTreeData`, `Ladder49_jt_kkt_z`), not lane-B theorem failures.
- Sessions 15-20 found the 28 Next1182 pairwise facts and B13 old/new dispatch
  structurally consistent; CI queue/infra gave no kernel verdict.
- Session 16 reproduced the census: 2506 terminals - 120 sharp - 1997 paid =
  389, with literal chunks 100/100/100/89.

## Retained engineering facts
- **ROOT-IMPORT REQUEST (only after CI green):** import
  `EnergyTerminalBatchB13Main` instead of `EnergyTerminalBatchB12Main`.
- Next1182 has 1182 members; pairwise checks compare at most two 168-element
  parts, and top membership dispatches through `Finset.mem_biUnion`.
- `Finset.card_biUnion` takes its disjointness hypothesis explicitly; pass it
  as `Finset.card_biUnion hdisj`.
- B11 straddles the 2565 boundary. If CI rejects B13, split B11 into B10 plus
  G03-G12 rather than assuming an interval.
- `Finset.disjoint_left.mp` needs `(a := a)` in these generated proofs.
- Emitters: `emit_next1182_top.py`, `emit_residual_census.py`; the latter
  reproduces the old census bytes and all count assertions.
- Mathlib-probe attempts gave no verdict (timeouts); CI is the only Lean-build
  authority for project modules.
