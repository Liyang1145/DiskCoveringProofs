EXPERT (2026-10-31): All seven `FrozenCapRowCap*` targets are still red; exact 700/700 and hashes are diagnostics, not credit.
- `1409` still leaves raw `![...] 2` lookups after `norm_num [rowA] <;> norm_num [y_1409, db]`; stop regenerating monoliths.
- Refactor 1409 only to prefix form: `weighted_rowA_eq_prefix (y) (i j) : Σ q, y q * rowA i j q = prefix j - prefix i`, where `prefix t = Σ q, if q.val < t.val then y q else 0`.
- Prove `prefix_1409 (t : Fin 10) : prefix t = cum_1409 t` by `fin_cases t <;> norm_num [y_1409, cum_1409, Fin.sum_univ_succ]`.
- Then prove `row_cap` by two prefix rewrites and `fin_cases i <;> fin_cases j <;> norm_num [cum_1409, db]`; this avoids 100 giant closed sums.
- Require `FrozenCapRowCap1409` exit 0 before applying the pattern to the other six; do not raise heartbeats or use native evaluation.
- Row caps alone move neither `x/2386` nor `0/7`: no count claim without an actual packet -> `Valid` -> residual/exclusion bridge.
- `hf0`/`hg`, the 382 absent payloads, MPacket validity, and the actual terminal-to-packet bridge remain unpaid.

# Lane C notes

## Standing constraints

- Kernel credit requires CI exit 0 and a mathematical consumer. Exact rational
  audits and hash/tree audits are diagnostics only.
- No `sorry`/`admit`/new `axiom`/`native_decide`/`ofReduceBool`/
  `implemented_by`/`maxHeartbeats 0`; do not edit frozen modules, root,
  lakefile, toolchain, or manifest.
- Keep green `FrozenCapRationalCore`, `PaidCellCertificateM`, and
  `PaidCellCertificateMCap` unchanged. Wrappers remain conditional on packet
  `hf0`/`hg`; only seven public residual HOST payloads exist and 382 are absent.
- `FrozenCapWideFieldWitnesses` is CI-green. Duplicate row-cap modules are
  CI-red or timed out and pay no credit. `ExcludedTree` is not a bridge to
  `RemainingTerminalRadius`.
- Do not replace exact roots/quantifiers with cached verdicts or decimals.
- POSIX `\b` in `rg` does not treat `_` as a word character: scan forbidden
  tokens without `\b` or independently inspect hits.

## Condensed status through 2026-10-30 part 159

- Exact B13 residual census is 389 ids. Seven public exclusions
  `{1409,2337,2341,2356,2360,2368,2370}` are residual and unpaid; no public
  payloads were found for the other 382 (not proof of external HOST absence).
- The wide-field family has exact checks for seven vectors, 700 row caps and
  strict `gain < T^2`. All row-cap arithmetic is diagnostics, not credit.
- Fifty-seven archive refinement drafts were found; 15 are forbidden, so no
  mass import. Restored source refinements include N0037, N2337, N2341,
  N3040, N2965, N3112, N3116, N3431, N3440, N3573, N3589, N3623, N3633,
  N3777, N3792, N3853. Their exact integer tree audits cover roots, terminals
  and split counts only, never MPacket validity or kernel exits.
- Conditional singleton wrappers/Mains and the RefineSeven/Eight/Eleven
  aggregates are CI green, including `paid_count` theorems with the refined
  premise and `remaining_of`. N0037/Twelve, N3112/N3116/N3431/N3573 and newer
  wrappers remain CI pending unless LATEST explicitly records exit 0. No root
  import was changed.
- `FrozenCapRationalCore` and `PaidCellCertificateM{,Cap}` are CI green.
  Seven public-tree exclusions and their row caps remained CI pending/red.
  Old row-cap failures included redundant follow-up tactics and nested-vector
  `dbmVal` lookups; part 159 replaced the latter by scalar `db` and one
  `norm_num [y, rowA, db]` per leaf, but that exact six-hash version was never
  successfully kernel-checked in CI.
- Missing throughout: row-cap kernel exits, public-tree bridge,
  packet/no-cell and exclusion-to-radius bridges, 377 residual ids conditional
  on pending wrappers, MPacket validity, energy and seven-class premises.

## 2026-10-31 - part 160 (row-cap proof reduced to signed intervals)

Kept the seven public target names but shortened each of the 700 leaf proofs.
For fixed `i j`, `rowA i j q` is `1` on `i ≤ q < j`, `-1` on `j ≤ q < i`,
and `0` elsewhere. Each leaf now gets a first `norm_num [rowA]` pass followed
by the narrow `norm_num [y_N, db]` pass, so `rowA` and its 90 conditional
tests do not enter the rational normalizer. This is a proof
engineering change only: theorem statements and `row_cap` consumers are
unchanged.

Files: `n11-work/ops/lanes/C/emit_frozen_cap_row_caps.py` SHA256
`b5ee747f343457548ac1d45a33a7e865a391606ca9b3b35104b8933661b752f6`;
row-cap SHA256:
`1409` `7f7341a56cc937656efc703defc6204e69c9919dc6f2a9dcc17d8e61c58e5536`,
`2337` `2f0fd8b8ac86f85346cd863a85e8fcd14a9d412cf5a4f256fef25dbe7e160ede`,
`2341` `f17ef0d19f75c3165c0ae45d6e1298dd8c8c70b23b19517ad4286e03f1e9776b`,
`2356` `6f7afa6856f7dc66e662f822b68bbac69d09a70594125959011ffa93c4c88bfc`,
`2360` `9cf7a20417f643a3826d9796968be07e6152f96d7d852ea96f4433ac07f5998f`,
`2368` `497abc879eb731b102990f4ea951fef56080d9c0c33b1c26b4aa1bd6b9429e3d`,
`2370` `85f82f22ce8a7d675e337b27737f293643b01999bc925c8f2ffa89fa10187695`.

Checks: emitter exit 0; 700/700 exact caps pass with global minimum slack
0; DBM SHA256 `BD4E71CB29804A5A3D5953727558F4656D23253A83B69F5C3D6E25EEB4EA8ED5`;
`py_compile`, `git diff --check` exit 0; forbidden-construct scan had no
matches (`rg` exit 1, expected). A direct core
Lean syntax probe was inconclusive because the shared 2-core sandbox timed out
even on a deliberately failing one-line file; therefore **no local Lean
syntax/kernel claim**. All seven are **CI pending** at the new hashes.

Still unproved/missing: kernel exits for all seven row-cap modules and the
public excluded tree; bridge to `RemainingTerminalRadius`; packet/no-cell and
exclusion-to-radius bridges; 382/377 residual energy ids depending on pending
wrapper accounting; MPacket validity; energy and seven-class premises.

Next: run CI with 1409 first. If the first pass is rejected, replace only that
line by `simp only [rowA]` and retain the narrow `norm_num [y_N, db]`; if 1409 exits
0, proceed to 2356 and check whether its heartbeat failure is gone. Do not
bulk-rewrite tactics before one new-hash row-cap exit 0.
ROOT-IMPORT REQUEST: none.

## 2026-10-31 - part 161 (sequenced leaf normalization; CI pending)

Replaced each leaf's unconditional two-line normalizer with
`norm_num [rowA] <;> norm_num [y_N, db]`. If the first pass closes a zero-slack
leaf, `<;>` runs nothing on the absent goal; otherwise the narrow scalar second
pass runs. This directly addresses the prior `No goals to be solved` failure
without merging `rowA`'s conditional tests into the large rational normalizer.
Regenerated all seven modules. Emitter SHA256
`af5c43c5f7c6c239146198307c4f4e6eff526108ea4f564f9a9c1e6da4805d08`.
Module SHA256 (all CI pending):
`1409` `9ec002a1387f3f5356c8ae366ab9aa429bc364baad4e5d2b78f9fb2d86cd6f0a`,
`2337` `f67446369d4653925aabfaa199d4f700978049234da8210e0af2f160fc9eb8f3`,
`2341` `988f674973750fc721afc3922e132f7b7dd6597e15dd6cecf998c6a50925cfc6`,
`2356` `25ea125f8acfb1c835ed99bb979487f359ec1bb0d38ff354d6b6cc43c4cb567d`,
`2360` `f6830a2a97d6a0e242cb8904c7647cab580e35c5209f3e1d2324eba62237cd6a`,
`2368` `90db2e7160c4cdfaa36f2cbb9e6ac2114128f84be63a6e6a6a8863c52a951b23`,
`2370` `09aa0b601ba8d2f5f425645e73d415bf734a506a5b7d68be35765062dda82a3f`.

Checks: emitter exit 0; 700/700 exact caps pass, global minimum slack 0; DBM
SHA256 `BD4E71CB29804A5A3D5953727558F4656D23253A83B69F5C3D6E25EEB4EA8ED5`;
`py_compile` and `git diff --check` exit 0; forbidden-token scan found no
matches. A Mathlib-probe tactic file was drafted, but the probe timed out at
120 s before Lean returned, so there is **no local kernel/syntax claim**.

Still unproved/missing: kernel exits for all seven row caps and the public
excluded tree; row caps to `RemainingTerminalRadius`/public-tree bridge;
packet/no-cell and exclusion-to-radius bridges; remaining residual ids;
MPacket validity; energy and seven-class premises.

Next: CI 1409 alone first. A fresh CI trace is authoritative: if 1409 is green,
check 2356 next; if red, use its first actual source line (not the stale
run-41123531381 trace) to choose the next narrow tactic change.
ROOT-IMPORT REQUEST: none.

## 2026-10-31 - part 162 (bounded leaf probe; no new credit)

Re-verified the part-161 emitted proof shape in
`FrozenCapRowCap1409.lean`: every leaf uses
`norm_num [rowA] <;> norm_num [y_1409, db]`. Built a Mathlib-only probe from
the exact `y_1409` definition, the 100-case `db`, and the first emitted leaf
(`row_cap_1409_0_0`). `timeout 60 lake env lean RowCap1409Probe.lean` exited
124 with no diagnostics. This is an infrastructure/probe timeout, **not** a
syntax or kernel verdict, and no source hash changed from part 161.

Checks: probe only, scope bounded to one leaf in `/workspace/tools/mathlib-probe`;
60 s timeout, exit 124. No project module was built locally. No new exact-arithmetic
audit was needed because the target and emitted bytes are unchanged.

Still unproved/missing: kernel exits for the seven row caps and public excluded
tree; public-tree/radius bridges; residual energy ids; MPacket validity; energy
and seven-class premises.

Next: trigger CI with only `N11Formalization.FrozenCapRowCap1409` in the active
serial target region (keep the dependency tree out of that first trial), then read
the first fresh source-level diagnostic. Do not bulk-rewrite the other six before
1409 has a fresh exit.
ROOT-IMPORT REQUEST: none.
