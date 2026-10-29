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

## 2026-10-29 — part 29 (condensed: CI-red diagnosis and core fix)

- Run `40818062141` was lane-C red despite a green workflow badge; its trailing
  `true` masks target exits. Core failed because the generated import list
  omitted `Mathlib.Algebra.BigOperators.Fin`; adding it made the core green.
- M's `of7` transport failed because `simpa only` omitted the source namespace
  projections. Core SHA256 at that checkpoint was `3ED6BB50...FC4E7C4`.

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

## 2026-10-29 — parts 40-42 (condensed: M transport history)

- M's `of7` transport now uses definitional `hW`/`hs`/`hi` plus `rw`; latest CI
  run `40893868710` reports `=== EXIT N11Formalization.PaidCellCertificateM 0`.
- Bounded Mathlib probes remained startup-timeout inconclusive; no local kernel
  verdict was obtained.

## 2026-10-29 — parts 43-45 (condensed: MCap transport iterations)

- CI `40893868710`: M green, MCap red at the old `rw [rho]` sites. Successive
  repairs localized `weighted_reduced_le` into a `calc`, added the missing
  inner `Finset.mul_sum`, and changed the final order step to
  `hrho.trans_le hlam`; statements and inputs unchanged.
- Exact-rational Python check of the identity: 1000 random cases, m in
  {1,2,5,9,16}, PASS (algorithm evidence, not Lean). The seven row caps still
  exact-check 700/700 with `global_min_slack 0`.
- `project_status.py --check`, `git diff --check`, and `py_compile` exited 0.
  Mathlib startup timed out and no project `.olean` exists, so MCap stayed
  **CI pending**; all seven row-cap kernels/bridges/wrappers/`hf0`/`hg` unpaid.

## 2026-10-29 — part 46 (MCap identity made definitional; CI pending)

- In `PaidCellCertificateMCap.weighted_reduced_le`, replaced the per-summand
  `unfold rho; rw [Finset.mul_sum]` step with direct
  `simp only [rho, Finset.mul_sum]`. This preserves the exact statement and
  numeric inputs while avoiding the rewrite failure at the old `rw [rho]` site.
- MCap SHA256 now
  `47f3340796ec555e495bddedfb33f63b2f1e96b76cc947684f7ad94da8bf70da`.

Checks (scope stated):
- `python tools/project_status.py --check`: exit 0 (handoff index/manifest
  declarations only; not math or full file integrity).
- A Mathlib-only `Finset` identity probe was written to `/tmp/CProbe.lean` and
  run under `timeout 120 lake env lean`; it exited 124 at startup, so it gave
  **no Lean verdict**.
- `git diff --check` exit 0; forbidden-token scan over MCap clean.
- No project `.olean` build; MCap remains **CI pending**, not paid. Energy
  count unchanged.

Still unproved / missing: MCap kernel verdict; seven row-cap kernels, tree
bridges, conditional wrappers, packet `hf0`/`hg`, 5-to-9-field rescue, and 382
HOST records.

Very next concrete step: require exactly `=== EXIT
N11Formalization.PaidCellCertificateMCap 0`; if green, add only
`N11Formalization.FrozenCapRowCap1409` to TARGETS and inspect its first
diagnostic.

## 2026-10-29 — part 47 (MCap CI diagnostics matched old source; calc replacement)

Did:
- Compared `ops/ci/LATEST.md` errors against `git show HEAD:...MCap.lean`:
  run `40893868710` built the pre-part-46 source. Its `40:8` and `71:36`
  failures are exactly the old `rw [rho]` and `by rw [hrho]` sites, not the
  current working-tree proof.
- Current proof replaces those sites with a four-step `calc`: unfold `rho`
  by `simp only`, commute finite sums, distribute `Finset.mul_sum` per row,
  and finish with `hrho.trans_le hlam`. Statement/inputs unchanged.

File SHA256:
- `n11-work/lean/N11Formalization/PaidCellCertificateMCap.lean`
  `47f3340796ec555e495bddedfb33f63b2f1e96b76cc947684f7ad94da8bf70da`.

Checks (scope stated):
- `python3 tools/project_status.py --check`: exit 0 (handoff/manifest declarations only).
- Static source inspection only; no Lean/kernel verdict for the current bytes.
- Existing deterministic exact-rational checks remain: 1000 identity cases
  and 700/700 row caps, `global_min_slack 0` (Python, not kernel).
- CI run `40893868710` result applies to old MCap bytes; current MCap is
  **CI pending**.

Still unproved / missing: current MCap kernel verdict; row-cap kernels, tree
bridges, conditional wrappers, packet `hf0`/`hg`, 5-to-9-field rescue, 382
HOST records. Energy count unchanged.

Very next concrete step: CI-build only current MCap and require
`=== EXIT N11Formalization.PaidCellCertificateMCap 0`; if green, add only
`N11Formalization.FrozenCapRowCap1409` to TARGETS and inspect its first error.
