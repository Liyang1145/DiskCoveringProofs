# Lane C notes

## Standing constraints

- CI is the only kernel-verdict authority; local Lean startup is blocked/slow.
  Pay no energy/class credit until targeted modules are CI-green, wrappers are
  linked, and the 382 absent HOST records are supplied.
- `TARGETS.txt` gates Core, M, MCap, WideFieldWitnesses, WideFieldRowCaps.
  Do not target WideFieldExcludedTree until both wide modules are CI-green.
- Wrappers remain conditional on packet `hf0`/`hg`. Public residual payloads are
  exactly seven IDs; 382 HOST records are missing.

## Condensed history through part 88

- Core (`40861839784`), M (`40893868710`), and MCap (`40949277719`) are CI-green;
  axiom reports are clean. Exact HOST census/arithmetic found seven public residual
  records and no payload for the other 382 IDs.
- Earlier four/five-field sign reports were superseded by wide-support exclusion
  witnesses. The exact generator rechecks seven probability vectors, 700 ordered
  row caps, and seven strict `gain < T^2` margins with `Fraction` arithmetic.
- Run `40988698121` at `2fdf1a1c` made both wide modules red: seven old
  `strict_gain_*` declarations expanded `norm_num` directly and left unsolved
  goals. Parts 82-88 progressively replaced that expansion with core-theorem reuse;
  none of those bridges received a CI verdict.

## 2026-10-30 — part 89 (canonical seven-witness rewrite)

Did:
- Replaced all seven generated `strict_gain_*` sum-congruence/`change` bridges
  with one canonical line:
  `simpa only [yW_node, endpoint_node] using FrozenCapRationalCore.strict_gain_node`.
  This rewrites the wide witness alias and every endpoint equation directly in
  the green core theorem, eliminating 56 tactic lines and the unverified
  intermediate goal shape.
- Regenerated all three wide outputs. Exact checks: seven probability vectors,
  700/700 ordered row caps, seven strict negative gain margins, and zero minimum
  cap slack for each of the seven public IDs.
- Reconfirmed the 389-cell census: all seven public records already have exact
  arbitrary-row-cap certificates; 382 residual IDs have no public core payload.

Files / SHA256 (lowercase):
- `n11-work/ops/lanes/C/emit_wide_field_exclusions.py`
  `f2e4acd8223d6106d45b78f2f093e200b5b5c4598f1b881792f3af19a991aac6`.
- `n11-work/lean/N11Formalization/FrozenCapWideFieldWitnesses.lean`
  `90a5c86e94d99e77bce33775939f8b67cee05f12f2c2530b96093147c81b7cc6`.
- `n11-work/lean/N11Formalization/FrozenCapWideFieldRowCaps.lean`
  `f893482177b0eeeb2b74bb9f0d38b71a54bd606033e3b7af4acd3c5016d19e0c`.
- `n11-work/lean/N11Formalization/FrozenCapWideFieldExcludedTree.lean`
  `89f0bc8eb820b046dada09702e9d939a3b34fd90c212163e21eb8c76e5e4df37`.

Checks (scope): generator exit 0 with the exact counts/margins above;
`py_compile`, hard-rule scan (clean), `git diff --check`, and
`project_status.py --check` exit 0. Two bounded mathlib-probe launches timed out
at 180 s without output; these are **not** Lean/kernel verdicts. No local project
build was run.

Still unproved/missing: no CI run has checked part 89; WideFieldWitnesses and
WideFieldRowCaps remain uncredited; WideFieldExcludedTree is untargeted and
conditional on `hf0`/`hg`; 382 HOST payloads absent; no energy/class credit.

Next: obtain `=== EXIT 0` for both wide targets. On green, add
`N11Formalization.FrozenCapWideFieldExcludedTree` to `TARGETS.txt`; on red,
inspect only the first reported declaration and revert that declaration's bridge
to an explicitly typed equality proof.

## 2026-10-30 — part 90 (row-cap heartbeat split)

Did:
- Inspected run `40998371772` / job `123876728856` at `88918335` directly. The
  old `FrozenCapWideFieldWitnesses` has `=== EXIT ... 0`, but
  `FrozenCapWideFieldRowCaps` has exit 1. All seven failures are deterministic
  200000-heartbeat timeouts at the seven 100-case `row_cap_*` declarations; the
  run's workflow-level `success` is therefore **not** a green-row-cap verdict.
- Changed the generated row-cap proof from one `fin_cases i <;> fin_cases j`
  (100 cases under one declaration budget) to ten row lemmas of ten cases each,
  followed by a ten-branch dispatch. The exact caps, witness bytes, and theorem
  statements are unchanged. This gives each declaration a fresh 200k budget and
  an approximately 10x smaller tactic search.

Files / SHA256 (lowercase):
- `n11-work/ops/lanes/C/emit_wide_field_exclusions.py`
  `0b40b700c4f03a9e49cc029389a833bf8caf62a0b262696ae45f61d5de8cc052`.
- `n11-work/lean/N11Formalization/FrozenCapWideFieldWitnesses.lean`
  `90a5c86e94d99e77bce33775939f8b67cee05f12f2c2530b96093147c81b7cc6`.
- `n11-work/lean/N11Formalization/FrozenCapWideFieldRowCaps.lean`
  `375f66a83d43b9579cffc019d224e2976afcd46730e1fb2e0f1595c6cb014cee`.
- `n11-work/lean/N11Formalization/FrozenCapWideFieldExcludedTree.lean`
  `89f0bc8eb820b046dada09702e9d939a3b34fd90c212163e21eb8c76e5e4df37`.

Checks (scope): emitter exit 0 with 700/700 exact rational caps passing, minimum
slack 0 for all seven IDs, and seven strictly negative exact gain margins;
`py_compile`, hard-rule scan (clean), and `git diff --check` exit 0. No local
project build was run; the row-cap split and the part-89 canonical witness bridge
remain **CI pending**.

Still unproved/missing: CI exit 0 for the new row-cap bytes and for the canonical
part-89 witness bytes; WideFieldExcludedTree remains untargeted and conditional
on packet `hf0`/`hg`; 382 HOST payloads absent; no energy/class credit.

Next: on the next run require `=== EXIT 0` specifically for
`FrozenCapWideFieldWitnesses` and `FrozenCapWideFieldRowCaps`. If both are green,
add `N11Formalization.FrozenCapWideFieldExcludedTree` to `TARGETS.txt`. If a row
lemma still times out, split that row into five-case lemmas rather than raising
heartbeats.
