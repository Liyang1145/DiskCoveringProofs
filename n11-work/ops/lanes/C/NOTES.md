EXPERT (2026-10-30):
- Core/M/MCap are green; the current wide work adds no paid energy or class count.
- `yW_* = FrozenCapRationalCore.y_*`; the strict-gain repair is deduplication, not a new exclusion.
- Wrappers remain conditional on `hf0`/`hg`; no theorem derives these from `Valid`, and none links them to B13 RemainingTerminalRadius.
- Stop emitting duplicate wide/four/five witness and row-cap families. They are CI waste until the `hf0`/`hg` source premise is closed.
- Highest leverage: prove one unconditional statement, e.g. `no_valid_1409 : ¬ ∃ m p, Valid p ∧ p.nodeID = 1409`, from a fully specified actual packet.
- If `hf0`/`hg` cannot be derived or the result cannot enter the 389 census, mark the lane non-counting and change scope.
- The seven public energy residuals are not the seven metric classes; never report them as SevenClassExclusions credit.
- Only matching-source CI exit 0 is paid. Python exact checks, hashes, and conditional False theorems are not.

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

## Condensed history through part 71

- Core (`40861839784`), M (`40893868710`) and MCap (`40949277719`) are
  CI-green with `=== EXIT 0` and clean axiom reports only.
- Seven public residuals exist; 382 HOST payloads are absent. Exact
  four/five-field witnesses and their 700 row caps pass exact checks, but all
  witness/row-cap modules and conditional wrappers remain **CI pending**.
- Local Lean startup timeout is not a kernel verdict; only CI exits count.

## 2026-10-30 — parts 66-69 (condensed: wrapper drafts and target gate)

- Drafted four/five-field node wrappers with source-tree bridges; all remain
  conditional on packet `hf0`/`hg` (not supplied) and are not targeted.
- Re-ran the emitters: 500/500 four-field and 200/200 five-field caps pass with
  exact `Fraction` arithmetic, minimum slack 0; these are HOST checks only.
- Run `40949277719` pays Core/M/MCap only; it did not target either family.

## 2026-10-30 — part 70 (public residual audit and four-field row-cap target)

Did:
- Added `audit_residual_public_records.py` and ran it over all JSON/JSONL in
  `n11-work/evidence-20261014`, `n11-work/evidence-20261028`, and restored
  `build/n11-wip/assets/evidence`. It checked 702 files / 51,466,284 bytes.
- Exactly seven core residual records (`id`, `g`, `f0Lo`, mixture data) exist:
  1409, 2337, 2341, 2356, 2360, 2368, 2370, all only in
  `paid16-general-next512.json`. The other 382 residual IDs have no public or
  restored-WIP core payload; this is not evidence about maintainer HOST storage.
- Added the previously omitted `N11Formalization.FrozenCapFourFieldRowCaps` to
  `TARGETS.txt` now that MCap is CI-green. Wrapper modules remain untargeted.

Files / SHA256 (lowercase):
- `n11-work/ops/lanes/C/audit_residual_public_records.py`
  `b2eb07b723ff97a0a6001b367c334e137b4a78aafb22e91809cfb147ca7b31b4`.
- `n11-work/ops/lanes/C/residual-public-record-audit.json`
  `cb7f472e348bd05a7efec0c7dfd3418d3ffae281a5496b26a9128b7365133ec9`.
- `n11-work/ops/lanes/C/TARGETS.txt`
  `d1d84878c88065439bd5536741607425213485d5c8c07e74a3c7f63ea8df26ec`.

Checks (scope): audit exit 0 with exact assertions (7 payload records, expected
ID set, one file) and 382 missing; `py_compile` and `project_status.py --check`
exit 0 (index declarations only); `git diff --check` exit 0. No local Lean run.

Still unproved/missing: kernel exits for four-field witnesses/row caps and
five-field witnesses/row caps; then both wrapper families; old seven row
caps/bridges; packet `hf0`/`hg`; 382 absent HOST payloads. Energy unchanged.

Very next concrete step: inspect the completed run headed by `eb4e3021`; require
exact 0 for four-field witnesses/row caps before adding
`FrozenCapFourFieldExcludedTree`, and exact 0 for both five-field modules before
adding `FrozenCapFiveFieldExcludedTree`. Patch the first diagnostic if red.

## 2026-10-30 — part 71 (four-field emitter and proof-form repair)

Did: added `emit_four_field_witnesses.py`; regenerated all five four-field
witnesses from `residual-mixture-faces4.json` with exact checks. Unit sums now
use `norm_num [y4_*, Fin.sum_univ_succ]`, matching the green core. Re-ran the
four/five emitters: 500/500 and 200/200 caps pass exactly, minimum slack 0.

Files / SHA256 (lowercase):
- `n11-work/lean/N11Formalization/FrozenCapFourFieldWitnesses.lean`
  `04fd8ef977904026b6dde1f2e2a7af00a4e4130d1a4908d29f54c6156b51fe48`.
- `n11-work/ops/lanes/C/emit_four_field_witnesses.py`
  `08e5aa3111a32c9dcbdd826183c9de0ed64115f68345c1c6cbe5b1bdf7ca2e0e`.
- `TARGETS.txt` remains the seven-module gate; wrappers stay untargeted.

Checks (scope): emitter exit 0, exact 5-witness/500-cap assertions, second run
reproduced the Lean hash; `py_compile`, `project_status --check`, and
`git diff --check` exit 0. No local Lean build: modules remain **CI pending**.

Still unproved: kernel verdicts for four/five witness/row-cap modules; wrapper
families; packet `hf0`/`hg`; 382 absent HOST payloads. Seven public residuals
are exclusions, not paid IDs.

Next: require exact `=== EXIT 0` for the four/five targets, then patch the
first diagnostic before adding either `*ExcludedTree` wrapper.

## 2026-10-30 — part 72 (source cross-check and four-field wrapper repair)

Did:
- Added `audit_pending_certificate_sources.py`, which parses the emitted
  four/five-field DBM matrices and compares all 700 integer entries against
  `DBMSourceTreeData`, then rechecks each witness margin with exact `Fraction`
  arithmetic. All seven records match; the smallest margin is positive.
- Repaired `FrozenCapFourFieldExcludedTree.lean`: it had bridged the frozen tree
  to the old `FrozenCapRowCap<id>` matrices while applying the new
  `FrozenCapFourFieldRowCaps` caps. It now imports `DBMSourceTreeData` directly
  and proves five local `db_eq_tree_*` bridges to `db_<id>`, matching the
  five-field wrapper. Wrappers still require packet `hf0`/`hg` and remain off
  `TARGETS.txt`.

Files / SHA256 (lowercase):
- `n11-work/lean/N11Formalization/FrozenCapFourFieldExcludedTree.lean`
  `86d4880facb6fd98520f0350eda8d043963a8315d27035007bee7f09c82ddda6`.
- `n11-work/ops/lanes/C/audit_pending_certificate_sources.py`
  `cd666fb4ad5489172c569d3720bb949c4617ac3e8654caf185187360cf9a794c`.
- `n11-work/ops/lanes/C/pending-certificate-source-audit.json`
  `ab59708e14f177edee200468f51361073afbb69977a2b8433429c776d7da07f0`.

Checks (scope): audit rerun exit 0, 700/700 matrix entries equal and seven
positive exact witness margins; `py_compile`, `project_status.py --check`, and
`git diff --check` exit 0. HOST source checks only; **no kernel verdict**.

Still unproved/missing: CI exits for the four/five witness and row-cap modules;
both wrapper families (conditional on `hf0`/`hg`); old seven row caps/bridges;
packet `hf0`/`hg`; 382 absent HOST payloads. Seven residuals are exclusions,
not paid IDs; energy count unchanged.

Very next concrete step: require CI `=== EXIT 0` for the four/five modules; if
green, add `FrozenCapFiveFieldExcludedTree` and
`FrozenCapFourFieldExcludedTree` to `TARGETS.txt`, otherwise patch the first
kernel diagnostic.

## 2026-10-30 — parts 76/78 condensed (wide-support exclusions)

- Superseded the false four/five-field sign reports. The deterministic
  `emit_wide_field_exclusions.py` now emits seven gain-minimising wide-support
  witnesses, 700 exact row caps, and seven conditional node wrappers.
- Exact HOST checks: seven probability vectors; 700/700 caps pass; all seven
  `gain - T^2` margins are negative; minimum cap slack 0. These are algebra
  checks, not kernel verdicts. Only witnesses and row caps were targeted.

## 2026-10-30 — part 79 condensed (missing `endpointLo` import fixed)

- Added the missing `ConvexMinorantCore` import after auditing the isolated
  witness module; this removed an immediate kernel blocker. Its check results
  and bytes are superseded by part 82 below; it paid no kernel verdict.

## 2026-10-30 — parts 80/81 (weighted-term proof repair)

Did:
- Read the `7d401b42` failure at the declaration level: the four/five-field
  `strict_gain_*` proofs left unsolved goals after expanding nine products of
  huge rationals. Replaced that generated proof shape in the four-field,
  five-field and wide emitters with the green core's tested shape: exact
  `y*E = H` term table, `Finset.sum_congr`, rewrite, then `norm_num`.
- Regenerated all three families together. Exact HOST checks remain: five
  four-field witnesses and 500 caps, two five-field witnesses and 200 caps,
  seven wide witnesses and 700 caps; all caps pass and every strict margin is
  negative. Byte-identical rerun achieved for the deterministic outputs.

Files / SHA256 (lowercase):
- `n11-work/ops/lanes/C/emit_four_field_witnesses.py`
  `5eb0e47e1061334f1bc84fb2d8ddfe3adceab32326db7e30d5cf3164f88de64a`
- `n11-work/ops/lanes/C/emit_five_field_certificates.py`
  `d4fc0959cd692d527f86a3fd83f6bd94464c61512f55e2deb556abb00dd90527`
- `n11-work/ops/lanes/C/emit_wide_field_exclusions.py`
  `6b95a15f24d3818b64b61c72ecffc6297c49de3c05d81714dab6fc50cf798166`
- `FrozenCapFourFieldWitnesses.lean`
  `4d8f910d8ae99b9b96aa68494254df0ac81e8f6d0c4c911d882d86a72b508e92`
- `FrozenCapFiveFieldWitnesses.lean`
  `7141cb51f0f4980f523ddde7d12a9a84d487db777a5687dd2f5a153375d74fbb`
- `FrozenCapFiveFieldRowCaps.lean`
  `5ee01032ffc24fbf615007ae9cd2e961d1bd5bce071a88b94159447506cbc054`
- `FrozenCapWideFieldWitnesses.lean`
  `2e86b7de84803d7f3de0941c59277cb58ccdd0e78d7983fe8a94e51ba65c9b8b`

Checks (scope): all three emitters exit 0 with the exact assertions above;
`py_compile`, hard-rule scan, `project_status.py --check`, and `git diff
--check` exit 0. These are HOST algebra/emission checks, **not kernel verdicts**.
`TARGETS.txt` still gates only the two wide modules; no local project build.

Still unproved/missing: CI exit for both targeted wide modules; the wide
wrapper is conditional on packet `hf0`/`hg`; four/five-field modules are not
currently targeted; 382 HOST payloads absent; no energy/class credit.

Next: inspect the run for these bytes and require `=== EXIT 0` for
`FrozenCapWideFieldWitnesses` and `FrozenCapWideFieldRowCaps`. If green, add
`FrozenCapWideFieldExcludedTree` to `TARGETS.txt`; if red, patch only the first
reported declaration. Re-target four/five witness+row-cap modules only after
the wide gate.

## 2026-10-30 — part 82 (wide strict-gain proofs reuse green core)

Did:
- Established exactly that every `yW_<id>` equals `FrozenCapRationalCore.y_<id>`
  (all seven vectors, exact `Fraction`, zero differences).
- Replaced each generated wide `strict_gain_*` large-expansion proof with a
  nine-entry `yW = y` check followed by reuse of the already CI-green
  `FrozenCapRationalCore.strict_gain_*`; the endpoint bridge remains explicit.
  This removes the proof shape reported unsolved by run `40988698121`.

Files / SHA256 (lowercase):
- `n11-work/ops/lanes/C/emit_wide_field_exclusions.py`
  `4fae8958eaa9cc882130dac4134035f42f0f8b28ee626871e0609af38b4961b2`.
- `n11-work/lean/N11Formalization/FrozenCapWideFieldWitnesses.lean`
  `f4c758dd5bd039f24cb1f402e6e3d95f47bfeb2366b25b7ca96ab26d618fcc20`.
- Row caps `f89348…e19e0c`; excluded-tree wrappers `89f0bc…e4df37`;
  `TARGETS.txt` remains the two wide modules.

Checks (scope): emitter exit 0; 700/700 caps pass with minimum slack 0; all
seven exact `gain - T^2` margins are negative; rerun bytes identical;
`py_compile`, `project_status.py --check`, and `git diff --check` exit 0;
hard-rule scan found no hits. No kernel verdict (local probe startup blocked).

Still unproved/missing: CI exits for the two targeted wide modules; wrapper is
conditional on packet `hf0`/`hg`; 382 HOST payloads absent; no energy credit.

Next: require CI `=== EXIT 0` for `FrozenCapWideFieldWitnesses` and
`FrozenCapWideFieldRowCaps`; if green, target the wide excluded-tree wrapper.
