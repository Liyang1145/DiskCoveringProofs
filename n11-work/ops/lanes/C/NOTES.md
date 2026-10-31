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

## Earlier 2026-10-31 work (parts 160--163)

Row-cap proofs were progressively rewritten (narrow `rowA`, then `db` table
lookups removed). All variants remained CI-red/pending; part 164 has the
first fresh CI diagnostic. Four-field rescue sources were regenerated and
exact audits passed, but no row-cap kernel exit was obtained.
## 2026-10-31 - part 164 (row-cap leaves no longer normalize `db`; CI pending)

Fresh CI run `41150468008` at `24e434b4` gave exit 1 for all seven public
row-cap modules and `FrozenCapPublicExcludedTree`; the four-field modules were
not reached/recorded. Its first failure was
`FrozenCapRowCap1409.lean:132:608: unsolved goals` (46 diagnostics retained
in the summary, so the tail is truncated). Exact values were still sound.

Changed both row-cap emitters so every leaf first uses `change` to replace
`db i j` (or `db_N i j`) by its exact generated rational, then runs
`norm_num [rowA] <;> norm_num [y_N]`. Thus the leaf proof no longer asks
`norm_num` to reduce the 100-clause table; theorem statements and `row_cap`
consumers are unchanged. Regenerated all seven public row caps and the
five four-field caps.

Files/hashes (SHA256 lowercase): emitters
`ops/lanes/C/emit_frozen_cap_row_caps.py`
`caeeff1339fc97c31181be9a35dedc914d6c6d45705c93fa5098df26fce46540`,
`ops/lanes/C/emit_four_field_row_caps.py`
`dfe2749e6d585f0fb4a583f9ae185e19224116392916decb6ed2388e1461290b`.
Row caps: `1409` `d3add6e0f9bd4f3736a5fab7d2838a7b81128fd79e303a78f48ba807f15612bf`,
`2337` `3829a59a230f1c0ce338524c791d3fcf1ce1412441fd8364b8ea2511517eee64`,
`2341` `5ae36dbe11450e0b06006aa389e0cd2a9b6e3c72a5d50efb7607696539699fa6`,
`2356` `50d86c71cf6c1c867a1f7126d0c95c09ce5f1bea8180c74a31ff660b978b904f`,
`2360` `acbfb4773a03f5b6523c2287ea65cafb1c219fcdac0d49ac5560e2d6c1ccbf1c`,
`2368` `7ae2c476fa976442ccb0bebcb5e921283dbb963fae2aaadb6f597d71710365e1`,
`2370` `6a9f95bdc63b16fe07f394d3c26185688b28858774caeed7c0ca6d9f44f1faa5`;
four-field `a9538ba5db325ab450b28f54f93af90f2ccbcf2dc234738fb62a50fd28b8803a`.

Checks: emitter exit 0; 700/700 public and 500/500 four-field exact caps pass,
global/per-node minimum slack 0; DBM SHA256
`BD4E71CB29804A5A3D5953727558F4656D23253A83B69F5C3D6E25EEB4EA8ED5`;
`py_compile`, `git diff --check`, and forbidden-token scan exit 0 (scan found
no matches). Shared Mathlib probe was starved by concurrent lane builds and
timed out at 60/90 s with no diagnostics, so **no local Lean syntax/kernel
claim**. All eight modules remain **CI pending** at these hashes.

Still unproved/missing: kernel exits for all seven public and five four-field
row-cap modules; public/four-field excluded-tree exits and bridges to
`RemainingTerminalRadius`; packet/no-cell and exclusion-to-radius bridges;
`2356`/`2360` rescue-or-exclusion; the other 382 residual ids; MPacket
validity; energy and seven-class premises.

Next: fresh serial CI with `FrozenCapRowCap1409` first. If its `change` is
rejected, read the fresh source-level diagnostic; otherwise run all seven,
then `FrozenCapFourFieldRowCaps`, before touching excluded trees. Do not infer
a kernel pass from the exact audits.
ROOT-IMPORT REQUEST: none.

## 2026-10-31 - part 167 (part-166 leaf pattern local probe timed out)

Re-read the part-166 sources and isolated the new leaf pattern in the cached
Mathlib probe `RowCapChangeProbe.lean` (two leaves: `(0,1)` and `(5,4)`). Both
use exactly `change <exact rational lhs> ≤ <exact rational rhs>` followed by
bare `norm_num`, matching the regenerated modules. Two bounded runs of
`source /workspace/tools/env.sh && timeout 150 lake env lean
RowCapChangeProbe.lean` (and a warm-cache retry at 120 s) exited 124 with no
Lean diagnostic. This is only a local resource result: **no local Lean
syntax/kernel claim**.

Added `N11Formalization/FrozenCapRowCap1409Smoke.lean` (SHA256
`a4b3428e2526f8f488ddacc31e768fa08d0cc14fb50cc2a970ffb6060d8a985c`),
containing only the `(0,1)` and `(5,4)` leaves with the same exact-rational
`change`/`norm_num` proofs, and placed its target first in `TARGETS.txt`.
It is diagnostic only and earns no payment. `py_compile` and `git diff --check`
exit 0. The smoke module is **CI pending**.

Current maintained source hashes and exact-audit scope remain those in part
166. CI `LATEST.md` still stops at `24e434b4`, before the part-166 rewrites, so
all seven public row caps remain **CI pending** despite the 700/700 exact
rational checks. Missing obligations are unchanged: kernel exits for the
seven public, four/five-field row caps and excluded trees; bridges to
`RemainingTerminalRadius`; 382 residual ids; MPacket validity; energy and
seven-class premises.

Next: CI must build the smoke module first, then
`N11Formalization.FrozenCapRowCap1409`. If smoke passes, run the other six
public caps and then the four/five-field caps; if smoke fails, preserve its
first source-level diagnostic. Do not use the failed local probe as evidence
for or against the `change` proof.
ROOT-IMPORT REQUEST: none.

## 2026-10-31 - part 165 (five-field 2356/2360 emitted; CI pending)

Re-read the completed five-field report: `2356` and `2360` both PASS exact
rational rechecks on support `{1,3,4,6,8}` (coordinates in the JSON). Thus all
seven public residual ids now have an exact 4/5-field certificate, but none is
yet a kernel payment. Regenerated the two five-field row-cap modules with a
direct 100-case `db_N` table and 100 explicit leaves per node; the witness and
excluded-tree module bytes did not change. Added all three five-field modules
to `TARGETS.txt` before the public excluded tree.

Files/SHA256 (lowercase): emitter `320577b3c170d17265259f19fd1a50e47e75cc8ae86ead0e7115ba61abd3fc25`;
row caps `3bd971ee2e1fb719c8fa6ab4e30b1269a249d2b18c8b6e8c4e9bf01772e8256`;
witnesses `7141cb51f0f4980f523ddde7d12a9a84d487db777a5687dd2f5a153375d74fbb`;
excluded tree `0731b07e252e91ea307ffba92cbd95102a9c41c6d800830da602929956603b78`;
exact report `87a9003277b317dffbc369b4d3ee31b3e9e9c1a783b3a8c5e637640e74563590`.

Checks: emitter exit 0; 200/200 exact caps pass with per-node minimum slack 0;
both rechecked weights have sum 1, are nonnegative, and satisfy all 100 caps;
`py_compile`, `git diff --check`, and forbidden-token scan exit clean. A fresh
one-leaf Mathlib probe timed out at 120 s with no diagnostics, so there is **no
local Lean syntax/kernel claim**. All modules remain **CI pending**; current
`LATEST.md` predates the part-164/165 source hashes.

Still unproved/missing: kernel exits for the seven public, four-field and
five-field row caps, and all excluded trees; bridges to
`RemainingTerminalRadius`; the other 382 residual ids; MPacket validity; energy
and seven-class premises.

Next: fresh serial CI with `FrozenCapRowCap1409` first, then `2356`; if green,
run the five-field row caps next. Read the first fresh source diagnostic rather
than inferring a pass from the exact audits.
ROOT-IMPORT REQUEST: none.

## 2026-10-31 - part 166 (explicit rational row-cap leaves; CI pending)

Fresh CI diagnostic showed the part-164 leaves failing at the second tactic
(`norm_num [rowA] <;> norm_num [y_N]`), not at `change db`. Changed each of
the 700 public frozen-cap leaves to
`change <exact rational lhs> ≤ <exact rational rhs>` followed by bare
`norm_num`, so neither the `rowA` table nor vector lookup enters arithmetic.
Regenerated all seven public row caps; theorem statements and `db` remain
unchanged. This was a proof-engineering change only. Four/five-field emitters
were not changed in this part.

Files/SHA256 (lowercase): emitter
`ops/lanes/C/emit_frozen_cap_row_caps.py`
`b1aa8a1a05eed67837d9ea60ed1a41bac7e940761aa875de1d22aa70718122ef`;
row caps: `1409` `a7283d64f504864abb6590e68dab8de7f187d7f6f7d3a7ca1ddf970a43e1a011`,
`2337` `30986ade2ab3cbbcaf6f01eb2bfa6271f90fa0bdfece766bf9e05b525d668413`,
`2341` `139ce258b5b4c50a627702be5ce22df4215fe79db8a9eff7a2a3d9660f3e2c51`,
`2356` `bdb8adbb0a1b859b382b472028f0a0e383f9b50bc2a0d4f5cbe966eda250ac0c`,
`2360` `134fd457618cb08d2ce656bca435a29050197bc4d80bbaab67d4d4a05faad4d0`,
`2368` `d2f33991f35d4ef6d4f67df27a1fd6d31bfef0012692f848d1ad44fc422fbf73`,
`2370` `c98c0a27745af5da171809810dd4db29162402560c7f796d2610471982766227`.

Checks: emitter exit 0; 700/700 exact caps pass, global minimum slack 0;
DBM SHA256 `BD4E71CB29804A5A3D5953727558F4656D23253A83B69F5C3D6E25EEB4EA8ED5`;
`py_compile` and `git diff --check` exit 0; forbidden-token scan had no
matches (rg exit 1, expected). A local `lake env lean` attempt failed before
compiling this module because Lake tried to restore/checkout Mathlib over
untracked files; therefore **no local Lean syntax/kernel claim**. All seven
are **CI pending** at the hashes above.

Still unproved/missing: kernel exits for all seven row caps, four/five-field
row caps, and excluded trees; bridges to `RemainingTerminalRadius`; 382
residual ids; MPacket validity; energy and seven-class premises.

Next: fresh CI with `FrozenCapRowCap1409` first. If an explicit-rational
`change` is rejected, capture the first source diagnostic before touching the
other emitters; if green, proceed to `2356` and then the four/five-field caps.
Do not infer a kernel pass from exact audits.
ROOT-IMPORT REQUEST: none.
