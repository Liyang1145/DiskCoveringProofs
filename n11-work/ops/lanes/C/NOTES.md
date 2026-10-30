# Lane C notes

## Standing constraints

- CI is the only kernel-verdict authority; local Lean startup blocked. Pay no energy/
  class credit until targeted modules are CI-green, wrappers are linked, and the
  382 absent HOST records are supplied.
- TARGETS currently gate Core, M, MCap, WideFieldWitnesses, WideFieldRowCaps.
  Do not target WideFieldExcludedTree until both wide modules are CI-green.
- Wrappers remain conditional on packet `hf0`/`hg`. Public residual payloads are
  exactly seven IDs; 382 HOST records are missing.

## Condensed history through 2026-10-30 part 82

- Core (`40861839784`), M (`40893868710`), and MCap (`40949277719`) are CI-green;
  axiom reports are clean. Exact HOST census/arithmetic found seven public residual
  records and no payload for the other 382 IDs.
- Earlier four/five-field sign reports were superseded by wide-support exclusion
  witnesses. Current wide generator rechecks seven probability vectors, 700 ordered
  row caps, and seven strict `gain < T^2` margins using exact `Fraction` arithmetic.
- Run `40988698121` at `2fdf1a1c` made both targeted wide modules red: seven
  `strict_gain_*` declarations left unsolved goals after direct `norm_num` expansion.
- Part 82 replaced that expansion with reuse of the green core theorem, but the
  `simp`-then-`simpa` bridge was not itself CI-tested.

## 2026-10-30 — part 83 (canonical wide strict-gain bridge)

Did:
- Replaced each generated wide `strict_gain_*` bridge with a canonical
  `rw [show yW = y]`, then `simpa only [endpoint] using` the green
  `FrozenCapRationalCore.strict_gain_*`. This removes the untested `simp` state
  before the core theorem is applied.
- Regenerated all three wide outputs deterministically. Exact checks remain:
  seven vectors are probability vectors; 700/700 row caps pass; all seven
  `gain - T^2` margins are negative; minimum cap slack is zero.
- A bounded `/workspace/tools/mathlib-probe` check of the abstract rewrite shape
  timed out during Lean/Mathlib startup after 120 s with no output. This is not a
  Lean error verdict or kernel result.

Files / SHA256 (lowercase):
- `n11-work/ops/lanes/C/emit_wide_field_exclusions.py`
  `ed7c2ec0c0f04a3dc1f42f5507897f93c625f444796995f3654a4cc32b40794e`.
- `n11-work/lean/N11Formalization/FrozenCapWideFieldWitnesses.lean`
  `aac6ab2c8cf8ed6fc8d9b4367f5b25fd2f74a3be07bb8f2b9e832955e380c767`.
- `n11-work/lean/N11Formalization/FrozenCapWideFieldRowCaps.lean`
  `f893482177b0eeeb2b74bb9f0d38b71a54bd606033e3b7af4acd3c5016d19e0c`.
- `n11-work/lean/N11Formalization/FrozenCapWideFieldExcludedTree.lean`
  `89f0bc8eb820b046dada09702e9d939a3b34fd90c212163e21eb8c76e5e4df37`.

Checks (scope): wide emitter exit 0 with the exact counts/margins above;
`py_compile`, hard-rule scan (no hits), `project_status.py --check`, and
`git diff --check` exit 0. These are HOST/emission checks, **not kernel verdicts**.
No local project build was run.

Still unproved/missing: CI exit for WideFieldWitnesses and WideFieldRowCaps;
WideFieldExcludedTree is untargeted and conditional on `hf0`/`hg`; 382 HOST
payloads absent; no energy/class credit.

Next: require `=== EXIT 0` for both targeted wide modules. If green, add
`N11Formalization.FrozenCapWideFieldExcludedTree` to `TARGETS.txt`; if red,
patch only the first reported declaration.

## 2026-10-30 — part 84 (bridge audit and deterministic regeneration)

Did:
- Re-read the stale CI failure: the seven `unsolved goals` were the old
  `strict_gain_*` bodies that expanded `norm_num` directly. Part 83 had already
  replaced those bodies with the green-core bridge, but no CI run has seen it.
- Audited the bridge shape, generator, and downstream wrapper interfaces.
  The bridge rewrites `yW_*` to the core `y_*`, then rewrites the endpoint
  theorem under the sum and applies `FrozenCapRationalCore.strict_gain_*`.
  `PaidCellCertificateMCap.not_valid_of_frozen_cap` expects exactly the
  emitted `hf0`/`hg`/cap/strict-gain arguments used by the tree wrappers.
- Regenerated all three wide assets from the hash-pinned proposal and DBM
  source. Exact checks: 700/700 row caps pass; all seven weighted gains are
  strictly below `T^2`; minimum cap slack is zero. Output bytes match part 83.
- A dependency-free Lean probe of the abstract rewrite shape did not produce
  output before its bounded timeout. Lean startup was competing with another
  lane's local probe, so this is neither a Lean error nor a kernel verdict.

Files / SHA256 (lowercase, unchanged from part 83):
- `n11-work/ops/lanes/C/emit_wide_field_exclusions.py`
  `ed7c2ec0c0f04a3dc1f42f5507897f93c625f444796995f3654a4cc32b40794e`.
- `n11-work/lean/N11Formalization/FrozenCapWideFieldWitnesses.lean`
  `aac6ab2c8cf8ed6fc8d9b4367f5b25fd2f74a3be07bb8f2b9e832955e380c767`.
- `n11-work/lean/N11Formalization/FrozenCapWideFieldRowCaps.lean`
  `f893482177b0eeeb2b74bb9f0d38b71a54bd606033e3b7af4acd3c5016d19e0c`.
- `n11-work/lean/N11Formalization/FrozenCapWideFieldExcludedTree.lean`
  `89f0bc8eb820b046dada09702e9d939a3b34fd90c212163e21eb8c76e5e4df37`.

Checks (scope): emitter exit 0; `py_compile`, hard-rule scan, `git diff
--check`, and `project_status.py --check` exit 0. These are HOST/emission
checks, **not kernel verdicts**. No local project build was run.

Still unproved/missing: CI exit for WideFieldWitnesses and WideFieldRowCaps;
WideFieldExcludedTree remains untargeted and conditional on `hf0`/`hg`; 382
HOST payloads absent; no energy/class credit.

Next: obtain `=== EXIT 0` for both targeted wide modules. On green, add
`N11Formalization.FrozenCapWideFieldExcludedTree` to `TARGETS.txt` as the next
single CI step; on red, inspect only the first reported declaration, since all
seven bridges now share one shape.

## 2026-10-30 — part 85 (definitional witness alias)

Did:
- Removed the seven function-extensionality bridges. The emitter now defines
  `yW_<node> := y_<node>` (the exact core vector), derives `nonneg_<node>` and
  `sum_<node>` directly from the CI-green core theorems, and proves
  `strict_gain_<node>` by `change` to `y_<node>`, then
  `simpa only [endpoint_<node>]` using the green core strict-gain theorem.
  This leaves only the exact endpoint equality as generated arithmetic.
- Regenerated all three wide outputs. Exact emission checks unchanged: seven
  probability vectors, 700/700 row caps, all seven negative gain margins, and
  zero minimum cap slack. RowCaps and ExcludedTree bytes are unchanged.

Files / SHA256 (lowercase):
- `n11-work/ops/lanes/C/emit_wide_field_exclusions.py`
  `02bfdbb15106d6aec8a476f8fef7ebb7133283e5fbbeae4e01c5962d7eb05c87`.
- `n11-work/lean/N11Formalization/FrozenCapWideFieldWitnesses.lean`
  `5609c7006ed24cde37601570663c832c7b3cc354c58ce22f75937189d7cd0246`.
- `n11-work/lean/N11Formalization/FrozenCapWideFieldRowCaps.lean`
  `f893482177b0eeeb2b74bb9f0d38b71a54bd606033e3b7af4acd3c5016d19e0c`.
- `n11-work/lean/N11Formalization/FrozenCapWideFieldExcludedTree.lean`
  `89f0bc8eb820b046dada09702e9d939a3b34fd90c212163e21eb8c76e5e4df37`.

Checks (scope): emitter exit 0 with exact counts above; `py_compile`,
`git diff --check`, hard-rule scan (only `#print axioms`), and
`project_status.py --check` exit 0. A 90 s mathlib-probe startup timed out with
no output; this is **not** a Lean/kernel verdict. No local project build.

Still unproved/missing: CI exit for WideFieldWitnesses and WideFieldRowCaps;
WideFieldExcludedTree untargeted and conditional on packet `hf0`/`hg`; 382 HOST
payloads absent; no energy/class credit.

Next: obtain `=== EXIT 0` for both current wide targets. If green, add
`N11Formalization.FrozenCapWideFieldExcludedTree` to `TARGETS.txt`; if red,
inspect only the first reported declaration, since all seven strict-gain proofs
now share the definitional-alias shape.

## 2026-10-30 — part 86 (core alias for redundant weighted terms)

Did:
- Identified the only repeated wide-witness arithmetic outside the strict-gain
  bridge: each `weighted_terms_*` expanded `yW_* q * E_* q` and a giant `HW_*`
  numerator. Replaced `HW_*` by the definitional alias `H_*` and proved each
  `weighted_terms_*` directly with the corresponding CI-green
  `FrozenCapRationalCore.weighted_terms_*`. This removes seven redundant kernel
  arithmetic checks without changing the exported interface.
- Regenerated all three wide outputs. Exact checks remain seven probability
  vectors, 700/700 row caps, seven strict negative gain margins, and zero
  minimum cap slack.

Files / SHA256 (lowercase):
- `n11-work/ops/lanes/C/emit_wide_field_exclusions.py`
  `32627fc3d42b30bc0ed52354778f2f4f0df2ed8084db65d132b519ca23e7f780`.
- `n11-work/lean/N11Formalization/FrozenCapWideFieldWitnesses.lean`
  `4c3bb2d92d0afe829a3186d85c4d16d6fb6d3cd6d75ecb732c76fa0b8f502af8`.
- `n11-work/lean/N11Formalization/FrozenCapWideFieldRowCaps.lean`
  `f893482177b0eeeb2b74bb9f0d38b71a54bd606033e3b7af4acd3c5016d19e0c`.
- `n11-work/lean/N11Formalization/FrozenCapWideFieldExcludedTree.lean`
  `89f0bc8eb820b046dada09702e9d939a3b34fd90c212163e21eb8c76e5e4df37`.

Checks (scope): emitter exit 0 with the exact counts above; `py_compile`,
hard-rule scan (clean), `git diff --check`, and `project_status.py --check`
exit 0. These are HOST/emission checks, **not kernel verdicts**. No local
project build was run.

Still unproved/missing: no CI run has checked part 86. WideFieldWitnesses and
WideFieldRowCaps remain uncredited; WideFieldExcludedTree remains untargeted
and conditional on packet `hf0`/`hg`; 382 HOST payloads absent; no energy/class
credit.

Next: require `=== EXIT 0` for both current wide targets. If green, add
`N11Formalization.FrozenCapWideFieldExcludedTree` to `TARGETS.txt`; if red,
patch only the first reported declaration.

## 2026-10-30 — part 87 (direct core strict-gain application)

Did:
- Removed the remaining post-`change` `simpa only [endpoint_*]` from all seven
  generated `strict_gain_*` witnesses. After the definitional alias `yW_* = y_*`
  is exposed by `change`, the goal is exactly the CI-green core theorem, so each
  proof now ends with `exact FrozenCapRationalCore.strict_gain_*`.
- Regenerated all three wide outputs. RowCaps and ExcludedTree bytes are
  unchanged; exact checks remain seven probability vectors, 700/700 row caps,
  seven strict negative gain margins, and zero minimum cap slack.

Files / SHA256 (lowercase):
- `n11-work/ops/lanes/C/emit_wide_field_exclusions.py`
  `507204e8a311a120b2b3f10a66aa7a188b6e689d352b75182a86f59274626fd6`.
- `n11-work/lean/N11Formalization/FrozenCapWideFieldWitnesses.lean`
  `799a0e185b534da7d5a88e157ba6c3cc9c548afa41d70b80dcdf8d6f49fc4243`.
- `n11-work/lean/N11Formalization/FrozenCapWideFieldRowCaps.lean`
  `f893482177b0eeeb2b74bb9f0d38b71a54bd606033e3b7af4acd3c5016d19e0c`.
- `n11-work/lean/N11Formalization/FrozenCapWideFieldExcludedTree.lean`
  `89f0bc8eb820b046dada09702e9d939a3b34fd90c212163e21eb8c76e5e4df37`.

Checks (scope): emitter exit 0 with the exact counts/margins above;
`py_compile`, seeded hard-rule scan (clean), `git diff --check`, and
`project_status.py --check` exit 0. These are HOST/emission checks, **not kernel
verdicts**. No local project build was run.

Still unproved/missing: no CI run has checked part 87; WideFieldWitnesses and
WideFieldRowCaps remain uncredited; WideFieldExcludedTree remains untargeted and
conditional on packet `hf0`/`hg`; 382 HOST payloads absent; no energy/class credit.

Next: require `=== EXIT 0` for both wide targets. If green, add
`N11Formalization.FrozenCapWideFieldExcludedTree` to `TARGETS.txt`; if red,
patch only the first reported declaration.

## 2026-10-30 — part 88 (explicit endpoint-sum bridge)

Did:
- Found the mismatch behind the part-87 proof: `FrozenCapRationalCore.strict_gain_*`
  sums over `E_*`, while the wide theorem sums `endpointLo Dq DQ (G_*)`.
  Replaced the fragile post-`change` bridge with an explicit pointwise
  `Finset.sum_congr` rewrite using `endpoint_*`, then `change` and exact core
  application. This avoids relying on `simpa` unfolding through the sum.
- Regenerated all three wide outputs. Exact emission checks remain 700/700 row
  caps, seven probability vectors, seven negative strict-gain margins, and zero
  minimum cap slack.

Files / SHA256 (lowercase):
- `n11-work/ops/lanes/C/emit_wide_field_exclusions.py`
  `ee036c05c6b9a9396557508e1970702802d0bd4879660f75938d6e0ae1712e13`.
- `n11-work/lean/N11Formalization/FrozenCapWideFieldWitnesses.lean`
  `2e0d0358842b702682e71bd2a574b403de88740e6d28b16e9baf52dd74e3ce21`.
- `n11-work/lean/N11Formalization/FrozenCapWideFieldRowCaps.lean`
  `f893482177b0eeeb2b74bb9f0d38b71a54bd606033e3b7af4acd3c5016d19e0c`.
- `n11-work/lean/N11Formalization/FrozenCapWideFieldExcludedTree.lean`
  `89f0bc8eb820b046dada09702e9d939a3b34fd90c212163e21eb8c76e5e4df37`.

Checks (scope): emitter exit 0 with exact counts/margins above; `py_compile`,
hard-rule scan (clean), `git diff --check`, and `project_status.py --check`
exit 0. These are HOST/emission checks, **not kernel verdicts**. No local
project build was run.

Still unproved/missing: no CI run has checked part 88; both wide targets remain
uncredited; WideFieldExcludedTree is untargeted and conditional on `hf0`/`hg`;
382 HOST payloads absent; no energy/class credit.

Next: require `=== EXIT 0` for both wide targets. On green, add
`N11Formalization.FrozenCapWideFieldExcludedTree` to `TARGETS.txt`; on red,
inspect only the first reported declaration.
