EXPERT (2026-10-29):
- M is green and sound but pays no energy count.
- Fix MCap line 40 with `simp only [DBMMinorantDual.rho]`; line 71 cascade should resolve.
- Keep TARGETS to current three; add row caps/bridges/wrappers only after MCap is green.
- Unify FrozenCapCertificates F0/G/y/E with FrozenCapRationalCore; remove duplicate constants.
- After MCap, complete one node-pinned wrapper (1409) with hnode/hf0/hg/row_cap/bridge before broad rollout.
- Max credit is seven residual IDs while 382 HOST records are absent; do not claim class/energy credit until wrappers are green and linked.

# Lane C notes

## Standing guidance

- SUPERVISOR (2026-10-29 12:20 CST): CI cancelled; stop polling Actions.
  TARGETS stay `FrozenCapRationalCore`, `PaidCellCertificateM`,
  `PaidCellCertificateMCap`; do not target `FrozenCapCertificates` until the
  core is green.
## Condensed history through part 27

- The residual census reconstructs 389 IDs, but only seven have public
  `g/f0Lo/weights`: `1409,2337,2341,2356,2360,2368,2370`; 382 HOST records
  are absent. Census SHA256 `747447E2...E07F46`.
- `recompute_next512_formulas.py` checks 512 public records exactly (505 pass,
  seven fail). The older `<=4-field` miss was superseded by the corrected
  signed-row search in part 49.
  `certify_next512_row_cap.py` proves all 100 ordered-pair caps for arbitrary
  row count, tightest Python slack `7.39e-7` at 2356 (not kernel evidence).
- `emit_frozen_cap_row_caps.py` deterministically emits seven 100-cap row-cap
  modules; exact self-check is 700/700 with minimum slack 0. The tree bridge,
  seven node-pinned `FrozenCapExcludedTree*` wrappers, and packet `hf0`/`hg`
  remain **CI pending**. The wrappers are conditional on `hf0`/`hg`.
- Core emitter exact-checks all seven frozen witnesses. The core is now CI
  green; M/MCap/row-cap/bridge/wrapper kernel verdicts remain pending. Local
  Mathlib probing is unavailable (startup timeout), not a Lean error verdict.

## 2026-10-29 — part 29 (condensed)
- Launcher masking fixed conceptually; core needed the missing big-operators import.

## 2026-10-29 — sessions 30-33 (condensed history)

- Core is kernel-green in run `40861839784`; M/MCap are not. The seven-record
  exact emitter checks pass, and the MCap algebra (`lower = f0Lo - lamB + rmin`,
  `rho = sum_a lam_a * rowA`) is statically sound.
- Old lane-C run `40818062141` was red despite a green workflow badge; read the
  `=== EXIT` lines, because the trailing `true` masks failures.
- Bounded local elaboration is unavailable: Lake tries to clone/checkout Mathlib
  and exits 124 with no Lean verdict. This is not a red kernel result.

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

## 2026-10-29 — parts 36-39 (condensed: search correction and M transport)

- The old 5-field `pass_count=0` result is invalid (missing reversed-pair
  coefficients); corrected support `[1,3,4,7,8]` for 1409 is feasible, but the
  search was timeout-inconclusive. Supports 6-9 remain unsearched.
- Replaced M's failed `change` with definitional `simpa only`, then with the
  explicit `hW`/`hs`/`hi` transport now at lines 69-77. Statements and numeric
  inputs unchanged. M later became kernel-green in run `40893868710`.
- Reran the row-cap emitter: 7 modules, 700/700 exact caps, minimum slack 0.

## 2026-10-29 — parts 40-48 (condensed: MCap transport and audits)

- M is kernel-green in run `40893868710`. MCap's old `rw [rho]` sites failed;
  the pre-part-52 `weighted_reduced_le` used a four-step `calc`. Run
  `40901508838` showed pre-fix bytes only, so no false green was claimed.
- Added deterministic `verify_mcap_weighted_identity.py` (seed `20261029`):
  1000/1000 exact-rational cases pass for row counts 1,2,5,9,16. Re-ran the
  row-cap emitter: seven modules byte-identical, 700/700 caps, min slack 0.
- `project_status.py --check`, `py_compile`, and `git diff --check` exited 0.
  Local Lean probes exited 124 before startup and gave no kernel verdict.

## 2026-10-29 — parts 49-51 (condensed: four-field witness pipeline)

- Fixed the reversed-pair bug in `residual_mixture_faces4.py`; re-ran all
  seven records exactly. Five pass with four-field unit-sum weights and all
  100 caps: 1409 `[2,3,4,8]` `(1/4,1/4,1/4,1/4)` margin `~6.36e-4`; 2337
  `[1,3,6,8]` `(1/16,1/4,1/4,7/16)`; 2341 `[2,3,5,8]`
  `(1/8,1/4,1/4,3/8)`; 2368 `[1,3,6,8]` `(1/8,1/4,3/8,1/4)`; 2370
  `[1,5,6,8]` `(1/4,5/16,3/16,1/4)`. Only 2356/2360 fail at <=4 fields.
  `residual_mixture_faces4.py` SHA256 `B0824058...A16CD`;
  `residual-mixture-faces4.json` `FB632FE5...0AD0AD`.
- Emitted `FrozenCapFourFieldWitnesses.lean` (five `y4_*`, `nonneg_*`,
  `sum_*`, `strict_gain_*`; hash `F5572AC9...67E0A`) and deterministic
  `emit_four_field_row_caps.py` + `FrozenCapFourFieldRowCaps.lean`
  (500/500 exact caps, min slack 0; hashes `32D363E7...E5F02` and
  `774390A3...738E2`). Both Lean modules are **CI pending**, off `TARGETS.txt`
  until MCap is green. No kernel verdict.
- Checks: all emitters `py_compile`/run exit 0 with built-in exact assertions;
  `project_status.py --check` exit 0 (declarations only). HOST-only evidence.

## 2026-10-29 — part 52 (MCap additivity repair; CI diagnostic exact)

Did:
- Read the archived full log for run `40914236268` (commit `95df31a3`), not a
  verdict from the workflow badge. M is kernel-green there. MCap failed only at
  `PaidCellCertificateMCap.lean:79:6`: `add_le_add_left` produced
  `rhoSum + A ≤ lamB + A`, while the calc goal needs
  `A + rhoSum ≤ A + lamB`.
- Replaced that one tactic line with `linarith [hrho.trans_le hlam]`. The goal
  is precisely ordered additive cancellation; no statement, numeric input,
  frozen source, target list, root, lakefile, or toolchain changed.
- Inspected the 1409 tree wrapper. Its `hf0`/`hg` remain genuine packet-input
  hypotheses: `hnode` alone does not determine `W`, `slopeQ`, or `interQ`.

Files / hashes:
- `n11-work/lean/N11Formalization/PaidCellCertificateMCap.lean`
  `D859711ACE44FDC7C3337EC326FA34EF6A28047704F010BD421A9E1A166B20DF`.
- `n11-work/ops/lanes/C/mcap-weighted-identity-check.json` regenerated with
  the new module hash (deterministic verifier).

Checks (scope stated):
- `python3 tools/project_status.py --check`: exit 0 (declarations only).
- `python3 verify_mcap_weighted_identity.py`: exit 0, 1000/1000 exact-rational
  cases PASS across row counts 1/2/5/9/16; HOST algebra evidence, not kernel.
- `git diff --check`: exit 0. Forbidden-token scan on MCap: clean.
- A bounded `/workspace/tools/mathlib-probe` `linarith` probe exited 124 before
  Lean startup; it supplies **no** kernel verdict. Current MCap is **CI pending**.

Still unproved / missing: current MCap kernel verdict; kernel verdicts for the
five four-field witnesses and their 500 caps; seven original row-cap kernels,
tree bridges, conditional wrappers, packet `hf0`/`hg`, 5-to-9-field search for
2356/2360, and 382 absent HOST records. Energy count unchanged.

Very next concrete step: supervisor commits this worktree and CI builds only
current `PaidCellCertificateMCap`; require exactly
`=== EXIT N11Formalization.PaidCellCertificateMCap 0`. If green, add only
`FrozenCapFourFieldWitnesses` to `TARGETS.txt`; if red, patch the next reported
line rather than broadening targets.

## 2026-10-29 — parts 54-58 (condensed)

- Corrected faces5 polytope search reproduces the 1409 four-field gain; full
  2356/2360 search still needs per-face checkpointing.
- Archived MCap failure was `linarith` normalization at old line 79. Current
  source uses `exact add_le_add_left (hrho.trans_le hlam) _`.
- Witnesses now depend on `FrozenCapRationalCore` + `PaidCellCertificateMCap`,
  not duplicate `FrozenCapCertificates`; five local `endpoint_*` bridges prove
  core `G` endpoints equal core `E`.
- Exact checks: MCap identity 1000/1000 (m=1,2,5,9,16); four-field row caps
  500/500, minimum slack 0.

## 2026-10-29 — part 59 (MCap/witness static audit)

Did: re-audited current MCap after the old-line-79 repair. The direct
`add_le_add_left` term matches the normalized goal. Traced each operand's
types: `hrho` rewrites the weighted `rho` sum to the `lamB` sum and `hlam`
applies row caps with nonnegative weights. Re-audited all five witnesses:
imports are core+MCap only, every `endpoint_*` bridges `G_<id>` to `E_<id>`,
and the `strict_gain` declarations use exact `y4` weights.

Files / hashes:
- `PaidCellCertificateMCap.lean`
  `47F3340796EC555E495BDDEDFB33F63B2F1E96B76CC947684F7AD94DA8BF70DA`
- `FrozenCapFourFieldWitnesses.lean`
  `07A1CB1D671F65759C04CE8B505CA86CAB87BB9B413B19A2E0603DA496C9AC42`
- `FrozenCapFourFieldRowCaps.lean`
  `774390A36A9B94AB95AF761963B62F5700A41FB05EFD9DAF7A5554327A6738E2`

Checks (scope stated): `project_status.py --check` exit 0 (manifest
declarations only); MCap exact verifier 1000/1000; `git diff --check` exit 0;
forbidden-token scan clean. No local Lean build or kernel verdict; MCap and
witnesses remain **CI pending**.

Still unproved / missing: MCap/witness/row-cap kernels, packet `hf0`/`hg`,
2356/2360 5-to-9-field rescue, 382 absent HOST records. Energy count unchanged.

Next: supervisor commits. CI must show exactly
`=== EXIT N11Formalization.PaidCellCertificateMCap 0`; if green add only
`FrozenCapFourFieldWitnesses` to `TARGETS.txt`. If red, patch its first new
diagnostic.

## 2026-10-29 — part 60 (MCap CI diagnostic reconciliation)

Did: compared run `40935785584` (commit `cea391a9`) with the worktree. The CI
failure at `PaidCellCertificateMCap.lean:79` is the old `linarith` source; the
current worktree has the narrow exact term
`add_le_add_left (hrho.trans_le hlam) _`. Rechecked its types against the goal:
`hrho.trans_le hlam : weighted rho sum ≤ lamB`, so the term yields
`endpoint sum + weighted rho sum ≤ endpoint sum + lamB`, definitionally the
calc goal. No new Lean source change was needed.

Checks (scope stated): static type/ordering audit of the current line 79 only;
CI summary/log inspected for run `40935785584`. No local kernel run and no new
CI verdict; current MCap remains **CI pending**.

Still unproved/missing: kernel verdict for current MCap; witness/row-cap
kernels, packet `hf0`/`hg`, 2356/2360 rescue, and 382 HOST records. Energy
count unchanged.

Next: supervisor commits the worktree; require exactly
`=== EXIT N11Formalization.PaidCellCertificateMCap 0`. If green, add only
`FrozenCapFourFieldWitnesses` to `TARGETS.txt`; if red, use its first new
diagnostic, not the superseded commit's line 79.
