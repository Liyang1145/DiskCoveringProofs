# Lane C notes

## Standing guidance

- SUPERVISOR (2026-10-29 12:20 CST): CI cancelled; stop polling Actions.
  TARGETS stay `FrozenCapRationalCore`, `PaidCellCertificateM`,
  `PaidCellCertificateMCap`; do not target `FrozenCapCertificates` until the
  core is green.
- EXPERT: M/MCap are sound but pay no energy count. The seven `excluded_*`
  theorems remain conditional without `hnode : p.nodeID = <id>` and proved
  `row_cap_<id>` lemmas. Test one id locally first; then bridge
  `FrozenCapCertificates` to the rational core. Do not claim class/energy credit
  while 382 public residual records remain absent.

## Condensed history through part 27

- The residual census reconstructs 389 IDs, but only seven have public
  `g/f0Lo/weights`: `1409,2337,2341,2356,2360,2368,2370`; 382 HOST records
  are absent. Census SHA256 `747447E2...E07F46`.
- `recompute_next512_formulas.py` checks 512 public records exactly (505 pass,
  seven fail); no extra-row or <=4-field gain rescue exists.
  `certify_next512_row_cap.py` proves all 100 ordered-pair caps for arbitrary
  row count, tightest Python slack `7.39e-7` at 2356 (not kernel evidence).
- `emit_frozen_cap_row_caps.py` deterministically emits seven 100-cap row-cap
  modules; exact self-check is 700/700 with minimum slack 0. The tree bridge,
  seven node-pinned `FrozenCapExcludedTree*` wrappers, and packet `hf0`/`hg`
  remain **CI pending**. The wrappers are conditional on `hf0`/`hg`.
- Core emitter exact-checks all seven frozen witnesses. The core is now CI
  green; M/MCap/row-cap/bridge/wrapper kernel verdicts remain pending. Local
  Mathlib probing is unavailable (startup timeout), not a Lean error verdict.

## 2026-10-29 — session part 28 (bounded local core elaboration attempts)
- `project_status.py --check` passed (declarations only); project/probe Lean
  timed out. Core then `c48270a5...65b7a5a`; no kernel verdict.

## 2026-10-29 — session part 29 (CI red diagnosed; two compile fixes)

Did:
- Inspected run `40818062141` / job `123308953128`. Its API/job conclusion is
  `success`, but the job log has `=== EXIT FrozenCapRationalCore 1`,
  `PaidCellCertificateM 1`, and `PaidCellCertificateMCap 1`. The workflow's
  unconditional `true` at the end of the build step masks target failures; the
  run is **CI red** for lane C and the success badge must not be cited.
- Core failure cause: all 14 uses of `Fin.sum_univ_succ` failed as an unknown
  constant because the generated import list omitted
  `Mathlib.Algebra.BigOperators.Fin`.
- `PaidCellCertificateM.of7_valid` failed at lines 65/68/69 because `simpa only`
  did not unfold `Paid16CellCertificate.PA/PB/W/slopeQ/interQ`. MCap's own build
  was then blocked by the missing M olean, not by a separate diagnostic.

Changes:
- `ops/lanes/C/emit_frozen_cap_rational_core.py`: added the missing import; reran
  it, which regenerated the core deterministically.
- `lean/N11Formalization/PaidCellCertificateM.lean`: added the source namespace
  definitions to the three `simpa only` sets.

Files (SHA256):
- `lean/N11Formalization/FrozenCapRationalCore.lean`
  `3ed6bb5026d4eeb00c6bc8cc3f350fb8d522c0414c592370fd3a91f36fc4e7c4`
- `lean/N11Formalization/PaidCellCertificateM.lean`
  `b0c1f6d583b5c4d748a281e14dc7289d75c2d761a95748fb59977fb8afa44072`
- `ops/lanes/C/emit_frozen_cap_rational_core.py`
  `10ecb5500eff5b22366910c4c01f4d3299bf4e5c841f917efe2c7e7ca1a87d93`

Checks run (scope stated):
- Core emitter: exit 0, deterministic output and frozen-source hashes printed.
- `git diff --check`: exit 0; forbidden-token scan over core/M/MCap: clean.
- No local Lean elaboration (Mathlib probe olean remains a 1128-byte stub), so
  the fixes are **CI pending**, not paid.

Still unproved / missing:
- Core, M, MCap, row caps, tree bridges, and seven wrappers still have no green
  kernel verdict. `hf0`/`hg` packet inputs and 382 residual HOST records remain
  absent; no energy count changes.

Very next concrete step: rerun CI and require `=== EXIT
N11Formalization.FrozenCapRationalCore 0`, then M and MCap 0; only after that add
`N11Formalization.FrozenCapRowCap1409` alone to `TARGETS.txt`. Do not infer a
green target from the workflow's overall badge.

## 2026-10-29 — sessions 30-32 (condensed; corrected CI still pending)

- Old run `40818062141` was red at all three targets due to the now-repaired
  missing `Mathlib.Algebra.BigOperators.Fin` import and old `of7_valid`
  simplifications. Pinned Mathlib `0df444a...` does define `Fin.sum_univ_succ`.
- Corrected run `40857762507` (head `0cb4f8de`, job `123392944402`) has had its
  `Build` step in progress throughout sessions 30-32. No target exit exists, so
  core/M/MCap remain **CI pending**, not green.
- Emitter reran twice after the fixes (exit 0): all seven records passed exact
  `Fraction` nonnegativity, unit-sum, frozen-source, weighted-term, and strict
  margin checks; regenerated core stayed byte-identical. Frozen inputs checked:
  `FlashCosineLeaf318` `08F36489...788A`, `Interval/Trig` `FB3DF66D...A04C`,
  `FlashCosineLeaf284Bridge` `C001704C...B1F8`.
- MCap transport was audited against `lower = f0Lo - lamB + rmin` and
  `rho = sum_a lam_a * rowA`; the weighted reduction, `lamB` bound, and
  strict-gain contradiction are algebraically sound.

SHA256: core `3ed6bb50...e7c4`, M `b0c1f6d5...4072`, MCap
`1697c1be...f6ea`, emitter `10ecb550...7d93`.
Checks: emitter exit 0, static declaration audit, `git diff --check` exit 0,
forbidden-token scan clean. No Lean kernel verdict.

Still unproved: no green core/M/MCap verdict; row caps, bridges, tree wrappers,
packet `hf0`/`hg`, and 382 HOST records remain unpaid.

## 2026-10-29 — session part 33 (bounded local check attempted)

Did: polled run `40857762507`; job `123392944402` is still `in_progress`, with
only `Build` marked `in_progress` and no target exit. Confirmed current core/M/
MCap SHA256 values exactly as above, `git diff --check` exit 0, and no forbidden
tokens in those three modules. Attempted bounded direct elaboration from
`n11-work/lean`: `timeout 110s lake env lean N11Formalization/FrozenCapRationalCore.lean`.
It exited 124 after ~110 s while Lake reported `info: mathlib: cloning
https://github.com/leanprover-community/mathlib4`; scope was local core only and
it produced **no Lean verdict**. The CI build remains the only candidate kernel
check.

Still unproved: same as above; in particular the core theorem set, M/MCap, all
seven row caps and tree wrappers, `hf0`/`hg`, and 382 HOST records.

Very next concrete step: read `=== EXIT N11Formalization.FrozenCapRationalCore`,
then M and MCap, from run `40857762507`. If all are 0, add only
`N11Formalization.FrozenCapRowCap1409` to `TARGETS.txt`; otherwise patch the
first reported core/M/MCap diagnostic. Do not treat local timeout as red.

## 2026-10-29 — part 34 (support audit; five-field search drafted)

Did:
- Re-audited the seven public residual witnesses in `FrozenCapRationalCore.lean`
  against `DBMSourceTreeData.lean` and the frozen proposal with exact
  `fractions.Fraction` arithmetic. All seven weight vectors sum to 1, satisfy
  all 100 ordered-pair caps, and have exact gain strictly below `T^2`.
  Supports are 1409 `[1,3,4,7,8]`, 2337 `[3,4,5,7,8]`,
  2341 `[1,3,4,6,7,8]`, 2356 `[1,3,4,5,7,8]`,
  2360 `[2,3,4,5,7,8]`, 2368 `[2,3,4,6,7,8]`,
  2370 `[3,4,5,7,8]`.
- Corrected the interpretation of the old <=4-field result: it excludes a
  **gain rescue**, not cap feasibility. Those face scripts correctly say
  "no <=4-field rescue"; the prior note's word "infeasible" was too strong.
- Added `residual_mixture_faces5.py`, an exact five-field vertex enumerator
  over all 126 supports and all 100 caps, with a PASS only when the exact gain
  exceeds the record threshold. It is a HOST-side search, not kernel evidence.

File SHA256:
- `ops/lanes/C/residual_mixture_faces5.py`
  `b94f4899205d4fc4f9dbacfb15421cb1acebdf94656c4620e14b41442b8a25be`.

Checks run (scope stated):
- Exact witness/audit snippet: 7/7 unit-sum, 7/7 all-100-caps feasible,
  7/7 strict-gain-failing; no Lean.
- `python3 -m py_compile residual_mixture_faces5.py`: exit 0.
- `timeout 50s python3 residual_mixture_faces5.py`: exit 124, no JSON emitted.
- A separate 25s node-1409-only run also exited 124 before any result. Both are
  **inconclusive**; no five-field margin or seven-record pass count exists.
- CI verdict still unavailable; do not claim any Lean kernel credit.

Still unproved / missing:
- No five-field rescue result yet; supports 6–9 were not searched.
- Core/M/MCap/row-caps/bridges/wrappers remain **CI pending**. Packet
  `hf0`/`hg` inputs and 382 HOST records remain absent. No energy-count change.

Very next concrete step: run `python3 -u residual_mixture_faces5.py` per node
under separate bounded timeouts (or precompute/cache the repeated rational
hyperspace determinants first), save partial per-node JSON, and report the exact
best five-field margin. Do not restart the full seven-record loop blindly.

## 2026-10-29 — part 35 (M projection fix after core-green CI)

Did:
- Read the public log archive for run `40861839784` (head `1a7c95c3`, HTTP 200).
  Exact target exits: `FrozenCapRationalCore 0`; `PaidCellCertificateM 1`;
  `PaidCellCertificateMCap 1` only because its M dependency failed. This is the
  first kernel-green core verdict; M/MCap are still **CI pending**.
- Diagnosed M's two errors at old lines 69/71 from the full log: `simpa [of7]`
  unfolded `of7 p` to a structure literal, but left `Paid16CellCertificate.W`
  versus the generic `W` unreduced under `rho`/`lower`. Expected/actual types
  differed there, not in the mathematics.
- Patched only `of7_valid` in `PaidCellCertificateM.lean`: `change` first exposes
  the common `p.rowFrom`/`p.rowTo`/`p.lam` arguments, then definitional `rfl`
  equalities `hW`, `hs`, `hi` transport `W`, `slopeQ`, and `interQ`; the final
  `simpa` closes from the corresponding frozen theorem. MCap source unchanged.

Files / hashes:
- `n11-work/lean/N11Formalization/PaidCellCertificateM.lean`
  `7b4115BE6CC89719129C4AE67D027D7F2BDC3E7C23FA7484E977731F9578CAEE`.
- `PaidCellCertificateMCap.lean` unchanged,
  `1697C1BE7034D9BB803A297C8105D3234BC536F610D88250687B6F282BB6F6EA`.

Checks (scope stated): full public CI log extraction (run above); `git diff
--check` exit 0; forbidden-token scan clean for both modules. No local Lean
verdict: direct `lean` startup exceeded a 10 s bound, so the kernel result is
**CI pending**.

Still unproved / missing: no kernel verdict for the M patch or MCap; row caps,
tree bridges, seven conditional wrappers, packet `hf0`/`hg`, five-to-nine-field
rescue, and 382 HOST records all remain unpaid. Energy count unchanged.

Very next concrete step: CI-build only `PaidCellCertificateM`; if green, build
`PaidCellCertificateMCap`. Only after both are exit 0, add
`FrozenCapRowCap1409` alone to `TARGETS.txt` and inspect its first diagnostic.

## 2026-10-29 — part 36 (five-field search; later invalidated)

Added per-node `--ids` runs and produced `pass_count=0` outputs for all seven
nodes. Those outputs are **INVALIDATED by part 37**: the support model omitted
negative coefficients of reversed ordered pairs. Do not cite their JSON files.

## 2026-10-29 — part 37 (five-field model corrected; rerun still open)

Did:
- Found that the old bitmask enumerator encoded only positive intervals
  `i <= q < j`. But `rowA(i,j,q) = [q<j]-[q<i]` is `-1` for reversed pairs.
  Replaced masks with the exact coefficient vector
  `bits[k]-bits[4]`, deduplicating by vector and keeping the minimum RHS.
  The simplex reduction is `x4 = 1-x0-x1-x2-x3`, bounded by
  `x0+x1+x2+x3 <= 1`.
- Corrected witness-support sanity check for 1409 `[1,3,4,7,8]`: `face5` now
  returns a feasible exact rational point and gain. The old model had falsely
  marked this support infeasible via a reversed-pair mask-0 row.

File / SHA256:
- `ops/lanes/C/residual_mixture_faces5.py`
  `3132f5456501b092dbc79ff20ac097309428cfc92c554de5a624f0dbf810f88d`.
- Stale `residual-mixture-faces5-*.json` artifacts were removed; regenerate
  from the corrected emitter before citing any figure.

Checks (scope stated):
- `python3 -m py_compile ops/lanes/C/residual_mixture_faces5.py`: exit 0.
- Corrected 3-node parallel rerun (1409/2337/2341) reached `timeout 120s`
  exit 124 with no output: **inconclusive**, not a verdict.
- Corrected single-node 1409 full 126-support run exceeded 150 s without
  output and was terminated: **inconclusive**.
- Exact frozen inputs remain proposal `F49F06FC...3DD16` and DBM
  `BD4E71CB...8ED5`; no Lean was run.

Still unproved / missing:
- No trustworthy <=5-field pass/fail count for any residual node yet; supports
  6-9 are unsearched. M/MCap/row caps/bridges/wrappers, packet `hf0`/`hg`, and
  382 HOST records remain unpaid.

Very next concrete step: profile corrected `face5` on one support, precompute
or cache its 4x4 determinant/inverse data across the 4-line combinations, then
rerun node 1409 alone under a fresh bound.
