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

## 2026-10-29 — parts 29-35 (condensed)

- Core became kernel-green in run `40861839784`; old lane-C run `40818062141`
  was red despite a green badge, so read `=== EXIT` lines. M's later transport
  patch became green in run `40893868710`; local Lake startup timeout is not a
  Lean verdict. MCap algebra and seven-record exact emitter checks passed.

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

## 2026-10-29 — parts 59-62 (condensed)
- MCap identity 1000/1000; four-field row caps 500/500. MCap line-79 failure was
  repaired through `linarith`. Five-field HOST rescues exist for 2356/2360.

## 2026-10-30 — parts 62-64 (condensed)
- Run `40949277719` exits core/M/MCap were `0`; MCap axioms were
  `[propext, Classical.choice, Quot.sound]`. Built MCap hash
  `d859711a…` matches the current source: **CI green / paid**.
- Four-field witnesses were added to `TARGETS.txt`; kernel is **CI pending**.
  Four-field 500 caps remain beyond this target gate.

## 2026-10-30 — part 65 (five-field Lean certificates drafted)

Did:
- Emitted the previously HOST-only five-field rescues for 2356/2360 as Lean
  witnesses. Exact supports are both `[1,3,4,6,8]`; weights are respectively
  `(1/8,1/8,1/4,1/4,1/4)` and `(1/8,3/16,3/16,1/4,1/4)`.
- Emitted their 200 ordered-pair caps from `DBMSourceTreeData.lean`, with
  nonnegativity, unit-sum, core endpoint bridges, and strict-gain theorems.
- Added both new modules to `TARGETS.txt`; kernel verdicts are **CI pending**.

Files / hashes (SHA256, lowercase):
- `n11-work/lean/N11Formalization/FrozenCapFiveFieldWitnesses.lean`
  `fad605054dbd5c3316ead05af2076bc6c03bc48a2dc9c99e2f37ae42117e655b`.
- `n11-work/lean/N11Formalization/FrozenCapFiveFieldRowCaps.lean`
  `5ee01032ffc24fbf615007ae9cd2e961d1bd5bce071a88b94159447506cbc054`.
- `n11-work/ops/lanes/C/emit_five_field_certificates.py`
  `876a3e1e918a9a0b00668e84012b255a6911a01724069f728ffb8495053ba1aa`.

Checks (scope): emitter exited 0 and asserted all 200 caps using `Fraction`
arithmetic, minimum slack 0; `py_compile` exit 0; forbidden-token scan clean;
`git diff --check` exit 0. These are generator/HOST checks, **not** a kernel
verdict.

Still unproved/missing: kernel verdicts for four-field witnesses/500 caps and
the new five-field witnesses/200 caps; packet `hf0`/`hg`; conditional wrappers;
382 absent HOST records. Energy count unchanged.

Very next concrete step: supervisor commit, then CI must report exact exits for
`FrozenCapFourFieldWitnesses`, `FrozenCapFiveFieldWitnesses`, and
`FrozenCapFiveFieldRowCaps`; patch the first failing diagnostic before adding
any more targets.

## 2026-10-30 — part 66 (five-field tree wrappers drafted)

Did:
- Confirmed the imported MCap source is exactly the CI-green hash
  `d859711a…` and re-ran the deterministic five-field emitter.
- Added `FrozenCapFiveFieldExcludedTree.lean`: two 100-entry source-tree
  matrix bridges (`decide +kernel`) and node-pinned `excluded_*_tree` wrappers
  feeding the five-field mixtures directly to `not_valid_of_frozen_cap`.
  The wrappers remain conditional on packet `hf0`/`hg`; neither is supplied.
  Not added to `TARGETS.txt`: its five-field prerequisites are still CI-pending.

Files / hashes (SHA256, lowercase):
- `n11-work/lean/N11Formalization/FrozenCapFiveFieldExcludedTree.lean`
  `0731b07e252e91ea307ffba92cbd95102a9c41c6d800830da602929956603b78`.

Checks (scope): emitter exit 0, regenerated bytes unchanged, 200/200 caps pass
with exact `Fraction` arithmetic and minimum slack 0; `py_compile` exit 0;
forbidden-token scan clean; `git diff --check` exit 0. No local Lean verdict.

Still unproved/missing: all five-field Lean kernels and wrapper bridge/wrapper
kernels; packet `hf0`/`hg`; four-field row caps; 382 absent HOST records.
Energy count unchanged.

Very next concrete step: after supervisor commit, inspect exact CI exits; if
five-field witnesses/caps are green, add only `FrozenCapFiveFieldExcludedTree`
and patch its first diagnostic if red.

## 2026-10-30 — part 67 (static audit of five-field draft)

Did:
- Audited `FrozenCapFiveFieldWitnesses`, `FrozenCapFiveFieldRowCaps`, and
  `FrozenCapFiveFieldExcludedTree` against the CI-green MCap theorem signature
  and the established frozen row-cap/wrapper pattern. The two wrappers pass
  `F0_*`, `G_*`, `y5_*`, nonnegativity, unit sum, row cap, and strict gain in
  the same order as `not_valid_of_frozen_cap`; source-tree bridges already
  rewrite the MCap `db` occurrence. No source defect identified statically.
- Did not widen `TARGETS.txt`: `FrozenCapFiveFieldExcludedTree` still depends on
  the three already-targeted five-field modules being kernel-green.

Checks (scope): bounded source inspection only; current CI report predates the
new targets. No kernel verdict for any five-field module. `hf0`/`hg` remain
unpaid packet hypotheses.

Still unproved/missing: exact CI exits for four-field witnesses, five-field
witnesses/row caps, and then the tree wrappers; four-field 500 caps; original
seven row caps/wrappers; 382 absent HOST records. Energy count unchanged.

Very next concrete step: inspect the next refreshed `ops/ci/LATEST.md`; require
exit 0 for `FrozenCapFourFieldWitnesses`, `FrozenCapFiveFieldWitnesses`, and
`FrozenCapFiveFieldRowCaps` before adding `FrozenCapFiveFieldExcludedTree` to
`TARGETS.txt`. Patch the first reported diagnostic if any are red.

## 2026-10-30 — part 68 (reproducibility recheck)

- Re-ran the five-field emitter: exit 0, 200 rows, per-node exact slack 0;
  all generated bytes unchanged (`fad60505…`, `5ee01032…`, `0731b07e…`).
  `TARGETS.txt` stays the six-module gate; CI predates the new targets.
- Still unpaid: all five-field kernel exits, four-field 500 caps, old row
  caps/wrappers, `hf0`/`hg`, and 382 absent HOST records. Energy unchanged.

## 2026-10-30 — part 69 (four-field tree wrappers drafted)

- Added `FrozenCapFourFieldExcludedTree.lean`: five node-pinned wrappers for
  1409/2337/2341/2368/2370, all conditional on packet `hf0`/`hg`.
- Reused `FrozenCapRowCapTreeBridges` after a 5×100-integer audit showed the
  four-field matrices are byte-for-byte the existing row-cap matrices.
- SHA256 `c6d10d813c62cbc5d53e15a3d44ee5d86555f8481f631b87d37e9e0d782a756a`.
  Not in `TARGETS.txt` until its two prerequisites are CI green. No Lean
  verdict; static/forbidden-token/`git diff --check` checks passed.
- Unproved: all new kernel exits, `hf0`/`hg`, 382 records; energy unchanged.
  Next: inspect exact CI exits; if four-field prerequisites are 0, target the
  wrapper module and patch its first diagnostic.
