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

## 2026-10-29 — parts 40-47 (condensed: MCap transport and stale CI)

- M is kernel-green in run `40893868710`. MCap's old `rw [rho]` sites failed;
  the current `weighted_reduced_le` proof uses a four-step `calc` with
  `simp only [rho, Finset.mul_sum]`, `Finset.sum_comm`, per-row `mul_sum`, and
  `hrho.trans_le hlam`. Statement and numeric inputs are unchanged.
- Run `40901508838` (commit `1b0171c4`, 15:26Z) still reported the old MCap
  failures at `40:8`/`71:36`; those bytes are pre-fix. Current MCap is
  **CI pending**, never claim it paid.
- Exact-rational Python evidence: 1000 random weighted-identity cases PASS;
  seven row caps exact-check 700/700 with `global_min_slack 0`.

Current MCap SHA256:
`47f3340796ec555e495bddedfb33f63b2f1e96b76cc947684f7ad94da8bf70da`.

## 2026-10-29 — part 48 (fresh deterministic row-cap audit)

Did:
- Re-ran `emit_frozen_cap_row_caps.py` under a 100 s timeout. It regenerated
  all seven `FrozenCapRowCap*.lean` files byte-identically: 700/700 ordered-pair
  caps, `global_min_slack 0` (1409 through 2370).
- Confirmed every CI error in `LATEST.md` belongs to the pre-fix MCap source;
  no new source change was justified without a kernel verdict.
- Added deterministic `verify_mcap_weighted_identity.py` (seed `20261029`):
  1000/1000 exact-rational cases PASS for row counts 1,2,5,9,16; report is
  `mcap-weighted-identity-check.json`. SHA256: script `884255C9...38CA2`,
  report `FF33B439...AB57`. This is algebra evidence, not kernel credit.

Checks (scope stated):
- `python3 tools/project_status.py --check`: exit 0 (handoff/manifest
  declarations only, not math or full-file integrity).
- `python3 -m py_compile` on the emitter and cap certifier: exit 0.
- `git diff --check`: exit 0; emitted seven modules and their hashes unchanged.
- Local `lake env lean` probe exited 124 at startup, so it gives **no Lean
  verdict**. No project build was attempted locally.

Still unproved / missing: current MCap kernel verdict; seven row-cap kernels,
tree bridges, conditional wrappers, packet `hf0`/`hg`, 5-to-9-field rescue, and
382 absent HOST records. Energy count unchanged.

Very next concrete step: CI-build current MCap bytes and require exactly
`=== EXIT N11Formalization.PaidCellCertificateMCap 0`. Only if green, add
`N11Formalization.FrozenCapRowCap1409` alone to `TARGETS.txt` and inspect its
first error.

## 2026-10-29 — part 49 (corrected <=4-field search: 5/7 exact gain witnesses)

Did:
- Found and fixed the reversed-pair bug in `residual_mixture_faces4.py`. The
  old `i <= field < j` mask dropped all negative `rowA` coefficients when
  `j < i`, so the previous "no <=4-field rescue" result was **invalid**.
  The generator now keeps both orientations via `row_a(i,j,field)` differences.
- Re-ran all seven records exactly (16.2 s). Five have nonnegative unit-sum
  weights, all 100 ordered-pair caps, and strict gain below `T^2`:
  1409 `[2,3,4,8]` weights `(1/4,1/4,1/4,1/4)`, margin `~6.362e-4`;
  2337 `[1,3,6,8]` `(1/16,1/4,1/4,7/16)`, `~4.084e-4`;
  2341 `[2,3,5,8]` `(1/8,1/4,1/4,3/8)`, `~3.702e-4`;
  2368 `[1,3,6,8]` `(1/8,1/4,3/8,1/4)`, `~3.091e-3`;
  2370 `[1,5,6,8]` `(1/4,5/16,3/16,1/4)`, `~5.074e-3`.
- Only 2356 and 2360 have no <=4-field rescue. Supports of size 5--9 remain
  unsearched. A direct exact check of 1409 on `[1,3,4,7,8]` also passes, with
  gain concentrated on `[1,3,4,8]`, but the fixed four-field search is sharper.

Files (SHA256):
- `residual_mixture_faces4.py`
  `b0824058ed1f40643a6385c8ad2348e263dbaf90017dd6a4b5c86b27b35a16cd`.
- `residual-mixture-faces4.json`
  `fb632fe52fbe9b89922f64fd99978926a897ad22998d7bcc305389f80b0ad0ad`.

Checks (scope stated):
- Corrected generator exit 0, `pass_count 5`; its built-in exact assertions
  rechecked unit sum, all 100 caps, gain, and strict threshold for every PASS.
- `python3 -m py_compile residual_mixture_faces4.py`: exit 0.
- `python3 tools/project_status.py --check`: exit 0 (declarations only).
- HOST-only rational evidence, not kernel credit. No local project Lean build.

Still unproved / missing: current MCap kernel verdict; row-cap/bridge/wrapper
kernels; packet `hf0`/`hg`; five-to-nine-field search; 382 HOST records.
Energy count unchanged.

Very next concrete step: emit the five new four-field `y` witnesses as a small
Lean module reusing `FrozenCapCertificates.F0/G/E` and prove `strict_gain` by
`norm_num`; keep it off `TARGETS.txt` until MCap is CI green.

## 2026-10-29 — part 50 (four-field witnesses emitted; CI pending)

Did: wrote `n11-work/lean/N11Formalization/FrozenCapFourFieldWitnesses.lean`
(SHA256 `f5572ac9d8fe357d431dd6de919d14b49c177630afc4b140c8df2f9abc967e0a`).
It defines `y4_{1409,2337,2341,2368,2370}` from the corrected exact
four-field supports, plus per-record `nonneg_*`, `sum_*`, and `strict_gain_*`
statements. `strict_gain_*` rewrites by the frozen `endpoint_*` equality and
closes by `norm_num`; it does not alter any frozen source or numeric value.

Checks (scope stated): source-only scan found all five definitions and
strict-gain declarations and no `sorry`/`axiom`; file hash recorded above.
No Lean build or kernel verdict was obtained. The module is deliberately
**CI pending** and is not in `TARGETS.txt` (MCap is still not CI green).

Still unproved / missing: current MCap kernel verdict; kernel verdict for the
four-field module; row-cap/bridge/wrapper kernels; packet `hf0`/`hg`;
five-to-nine-field search; 382 absent HOST records. Energy count unchanged.

Very next concrete step: after MCap CI green, add only
`N11Formalization.FrozenCapFourFieldWitnesses` to `TARGETS.txt` and build it;
then add `excluded_*` wrappers for these five witnesses.

## 2026-10-29 — part 51 (four-field row-cap emission)

Did: added deterministic `emit_four_field_row_caps.py` and generated
`FrozenCapFourFieldRowCaps.lean` for the five corrected four-field witnesses
(1409, 2337, 2341, 2368, 2370). It imports the witness module and proves all
500 ordered-pair caps exactly; every node has minimum Python slack 0.
Source SHA256:
- `FrozenCapFourFieldRowCaps.lean`
  `774390A36A9B94AB95AF761963B62F5700A41FB05EFD9DAF7A5554327A6738E2`.
- `emit_four_field_row_caps.py`
  `32D363E7B988BC1D6A20043E143BAB7098FC17802B353971439ACD89F72E5F02`.

Checks (scope stated): emitter `py_compile` and bounded run exited 0; its
built-in exact checks validated unit sum and 500/500 caps; `git diff --check`
exited 0. No Lean build/kernel verdict. Module is **CI pending** and remains
off `TARGETS.txt` pending MCap green.

Still unproved/missing: MCap kernel verdict; four-field witness and row-cap
kernels; node/tree wrappers for the new `y4` caps; 5-to-9-field search for
2356/2360; packet `hf0`/`hg`; 382 absent HOST records. Energy count unchanged.

Very next concrete step: after MCap and `FrozenCapFourFieldWitnesses` are green,
add `FrozenCapFourFieldRowCaps`, then emit node-pinned wrappers reusing the
existing `db_eq_tree_*` bridges and these new row_cap lemmas.
