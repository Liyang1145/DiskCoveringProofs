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

## 2026-10-29 — sessions 30-33 (condensed history)

- Core is kernel-green in run `40861839784`; M/MCap are not. The seven-record
  exact emitter checks pass, and the MCap algebra (`lower = f0Lo - lamB + rmin`,
  `rho = sum_a lam_a * rowA`) is statically sound.
- Old lane-C run `40818062141` was red despite a green workflow badge; read the
  `=== EXIT` lines, because the trailing `true` masks failures.
- Bounded local elaboration is unavailable: Lake tries to clone/checkout Mathlib
  and exits 124 with no Lean verdict. This is not a red kernel result.

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

## 2026-10-29 — parts 36-38 (condensed: five-field search and M transport)

- The old 5-field `pass_count=0` artifacts are invalid: they omitted negative
  reversed-pair coefficients. The corrected generator uses `bits[k]-bits[4]`;
  1409 support `[1,3,4,7,8]` is now feasible, but runs were still timeout-
  inconclusive. No trustworthy <=5-field count exists; supports 6-9 unsearched.
- `of7_valid` transport was changed from `change` to explicit `hW`/`hs`/`hi`.
  CI showed the `change` errors at old lines 69/71; that attempt never passed.

## 2026-10-29 — part 39 (M proof form corrected; row-cap emitter rechecked)

Did:
- Replaced the failed `change` block in `PaidCellCertificateM.of7_valid` with
  direct definitional `simpa only` over `of7`, lane `W/slopeQ/interQ`, and
  `Paid16CellCertificate` counterparts. Statements and numeric inputs unchanged.
- Reran the deterministic seven-node row-cap emitter; it regenerated all seven
  modules and exact-checked 700 ordered-pair caps, global minimum slack 0.

Files (SHA256):
- `n11-work/lean/N11Formalization/PaidCellCertificateM.lean`
  `b0c1f6d583b5c4d748a281e14dc7289d75c2d761a95748fb59977fb8afa44072`.
- `PaidCellCertificateMCap.lean` unchanged,
  `1697c1be7034d9bb803a297c8105d3234bc536f610d88250687b6f282bb6f6ea`.
- Row caps now `A41DC2BD...84EB` (1409), `6B5DB339...0409` (2337),
  `27C184EA...077F` (2341), `21588672...89C9` (2356), `2A057965...583C`
  (2360), `944C57D4...1DC3` (2368), `2FABE763...D0C` (2370).

Checks (scope stated):
- `python3 -m py_compile emit_frozen_cap_row_caps.py`: exit 0.
- Emitter output: 7 modules, 700 rows checked, `global_min_slack 0`; this is
  exact rational Python evidence, not a Lean/kernel verdict.
- `git diff --check`: exit 0. Forbidden-token scan over M/MCap: clean.
- No local Lean build attempted; M/MCap/row caps/bridges remain **CI pending**
  (core is the only kernel-green module). Energy count unchanged.

Still unproved / missing:
- M and MCap kernel verdicts; seven row-cap kernels, tree bridges, conditional
  wrappers, packet `hf0`/`hg`, 5-to-9-field rescue, 382 HOST records.

Very next concrete step: CI-build only M, require `=== EXIT
N11Formalization.PaidCellCertificateM 0`, then MCap. If both are 0, add only
`N11Formalization.FrozenCapRowCap1409` to `TARGETS.txt` and inspect its first
diagnostic.

## 2026-10-29 — part 40 (M proof transport corrected; CI pending)

- Old M failure was a `simpa` transport mismatch between the `of7` packet and
  `Paid16CellCertificate.W/slopeQ/interQ`; mathematics was unaffected.
  Replaced it with `hW`/`hs`/`hi` proved by `rfl`, then `rw` and the source facts.
- M SHA256 `FE19DB72F25113B78A9A098E43E4CBF0C103354AD19D61BF9510AA03CA9065F2`;
  MCap unchanged `1697C1BE...F6EA`. `git diff --check` and forbidden-token scan
  clean. No local Lean verdict: M/MCap are **CI pending**, not paid.
- Still unpaid: M/MCap kernels, row caps, bridges, seven wrappers, packet
  `hf0`/`hg`, 5-to-9-field rescue, 382 HOST records. Energy count unchanged.

## 2026-10-29 — part 41 (definitional transport audited)

- Re-read current M lines 58–78 and confirmed all three `rfl` transports unfold
  through `of7` to the same `Paid16CellCertificate` projections.
- `project_status.py --check` exit 0 (manifest/index declarations only, not math);
  `git diff --check` exit 0; M/MCap forbidden-token scan clean. No local kernel run.
- M remains **CI pending** at SHA256 `FE19DB...65F2`; MCap at `1697C1BE...F6EA`.

Very next concrete step: supervisor push, then require `=== EXIT
N11Formalization.PaidCellCertificateM 0` and MCap 0 before adding row-cap 1409.

## 2026-10-29 — part 42 (transport patch retained; bounded probe inconclusive)

- Re-read M lines 58–78: both `hp.reduced q` and `hp.numeric` now transport via
  definitional `hW`/`hs`/`hi` and `rw`, with no `change` or generic `simpa`.
- `project_status.py --check` exit 0 (manifest/index declarations only).
  `git diff --check` exit 0; M/MCap forbidden-token scan clean.
- M SHA256 `FE19DB72F25113B78A9A098E43E4CBF0C103354AD19D61BF9510AA03CA9065F2`;
  MCap unchanged `1697C1BE7034D9BB803A297C8105D3234BC536F610D88250687B6F282BB6F6EA`.
- A minimal `Mathlib` probe of the `rfl`+`rw` pattern hit the known 90 s Lake
  startup timeout (`EXIT:124`), so it gives no Lean verdict. M/MCap are **CI
  pending**, not paid.

Still unproved: M/MCap kernels, row caps, bridges, seven wrappers, packet
`hf0`/`hg`, 5-to-9-field rescue, and 382 HOST records. Energy count unchanged.

Very next concrete step: supervisor push, then require exactly `=== EXIT
N11Formalization.PaidCellCertificateM 0`; only then test MCap, then row-cap 1409.
