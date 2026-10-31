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

## Earlier 2026-10-31 parts 160--167 (superseded)

Row-cap proof variants (`change`, scaled leaves, five-field `2356`/`2360`)
all remained CI-red/pending; exact rational audits passed but paid no kernel
credit. Their `change`-based sources are superseded by parts 169 onward.

## 2026-10-31 - part 168 (seven-way exclusion consumer; CI pending)

Added `N11Formalization/FrozenCapPublicExcludedAggregate.lean`, which packages
the seven exact node/`f0Lo`/`g` hypotheses as one `PublicResidualData p`
proposition and proves `not_valid_of_public_residual`: this data plus
`PaidCellCertificateM.Valid p` implies `False`. It is a downstream dispatch
interface over the existing per-node tree theorems, not a new packet,
exclusion-to-radius bridge, or residual payment. Added its target immediately
after `FrozenCapPublicExcludedTree` in `TARGETS.txt`.

Files/SHA256 (lowercase): aggregate
`0f7c79985c62db79ce3d259b4e31542a705c63e8880e6c03b2f206f1e08b39da`;
existing public tree `e5ca5e2a1968d1d50538c0f6917284e9a101931fb44caf1a6f11e4679d9673a3`;
`TARGETS.txt` `582ac1407bf8524279dc7e0373555440f27d267bd59a8ce25380f79fc3d57ae6`.

Checks: three lane emitters pass `py_compile`; `git diff --check` exits 0;
forbidden-construct scan over the new module has no hit other than the
intentional `#print axioms` report line; no line exceeds 120 characters.
Local Lean is resource-unavailable this session: even core
`example : True := trivial` timed out at 45 s with no diagnostic, so there is
**no local syntax or kernel claim**. The new module is **CI pending**.

Still unproved/missing: CI exits for the seven row caps, four/five-field
modules, public tree and aggregate; bridges from exclusions to
`RemainingTerminalRadius`; packet existence/no-cell bridge; 382 residual ids;
MPacket validity; energy and seven-class premises.

Next: fresh serial CI must build the smoke leaf, then `1409`, then the public
tree and aggregate. If smoke exposes the first current source diagnostic,
preserve it before changing the emitter; do not infer a kernel pass from the
700/700 exact audit.
ROOT-IMPORT REQUEST: none.

## 2026-10-31 - part 178 (leaf type repair; CI pending)

Found a concrete defect in part 177: row aggregates `exact`-dispatched to
closed-rational leaf theorems, but the expected leaf type is the weighted sum
`∑ q, y q * rowA i j q ≤ db i j`. Restored sum-shaped leaves in all three
emitters while keeping the `fin_cases j` row dispatch. Fixed leaves use
`norm_num [y, rowA, db, Fin.sum_univ_succ]`; the prior failing site was the
variable-`j` row proof, now dispatched before the leaf tactic runs. The smoke
now exercises two real sum-shaped leaves (`0,2` and `5,4`), not closed numerals.

Files/SHA256 (lowercase): smoke
`0065e3b0c42264155557b414be0b23fa035c930983ec40f614574353e3f3b9cb`;
emitters `b440f898...` (public), `306b7979...` (four-field),
`212b0e31...` (five-field). Public caps: 1409 `9652ecf3...`, 2337
`fea8c1c6...`, 2341 `e87cf4ef...`, 2356 `5448644d...`, 2360 `76eb7183...`,
2368 `22390e0d...`, 2370 `a58bad28...`; four-field `fbc80eac...`,
five-field `5ab1d553...`. Five-field witnesses were regenerated unchanged
(`7141cb51...`). `TARGETS.txt` is unchanged because module names are stable.

Checks/scope: all three emitters exit 0; exact rechecks pass 700/700 + 500/500
+ 200/200 with per-node minimum slack 0; `py_compile`, `git diff --check`,
forbidden-token scan, and 120-column scan pass. Run `41181225934` / source
`69903c35` was still in progress and predates this repair, so it is not a result
for these hashes. No local Lean syntax or kernel claim (Mathlib probe lacks
the required project oleans). This revision is **CI pending**.

Still unproved/missing: kernel exits for all caps/trees/aggregate; exclusion
to `RemainingTerminalRadius`; packet existence/`Valid`; 382 payloads; MPacket
validity; energy and seven-class premises.

Next: supervisor commit and fresh serial CI. Read the first diagnostic from
smoke `0065e3b0...`, then `1409` `9652ecf3...`; if green continue through all
public caps, then four/five-field caps/trees.
ROOT-IMPORT REQUEST: none.

## 2026-10-31 - condensed parts 169/175 (superseded)

Run `41176805557` reached smoke exit 0 but `FrozenCapRowCap1409:520` left its
`Fin 9` sum unevaluated after `Fin.sum_univ_succ`; both earlier leaf/emitter
revisions are superseded by part 177.
## 2026-10-31 - part 171 (aggregate signature audit; CI pending)

Re-read part 170 and checked the new public aggregate against all seven tree
consumers. Every disjunct carries the exact node, `f0Lo`, and pointwise `g`
hypotheses; each `rcases` branch calls the matching `excluded_<id>_tree`, so
the interface introduces no radius or exclusion-to-payment claim. Static scan
of `FrozenCapPublicExcludedAggregate.lean`: 68 lines, longest 92 chars, no
forbidden construct, SHA256
`0f7c79985c62db79ce3d259b4e31542a705c63e8880e6c03b2f206f1e08b39da`;
`git diff --check` exits 0.

Checks/scope: source-signature inspection and static scans only. A bounded
20 s Mathlib-probe attempt (`False.elim` trivial check) timed out at 20 s with
no diagnostic, so there is **no local Lean syntax or kernel claim**. Aggregate
and all earlier row/tree targets remain **CI pending**; `LATEST.md` remains at
`24e434b4` and its row-cap diagnostics are stale.

Still unproved/missing: kernel exits for smoke, row caps, four/five-field and
public trees/aggregate; exclusion-to-`RemainingTerminalRadius` bridge; packet
existence/`Valid`; 382 residual payloads; MPacket validity; energy and
seven-class premises.

Next: supervisor commit for fresh serial CI. Require smoke then `1409` exit 0;
if red, preserve the first current-SHA source diagnostic before changing an
emitter. Do not treat exact rational audits as kernel payments.
ROOT-IMPORT REQUEST: none.

## 2026-10-31 - part 173 (definition-independent row leaves; CI pending)

The stale run `41168580187` failure was on the pre-part-172 `change` sources.
Since local Lean cannot import the project, the next repair removes the tactic
fragility rather than re-running the same unfolding: all three emitters now
substitute the exact `Fraction` row sum and exact cap RHS into each leaf, so
every leaf is a closed rational inequality proved by bare `norm_num` (no
`rowA`, `y_*`, or `db` unfolding). Theorem names, row sums, cap integer
matrices, and the generic `row_cap` interfaces are unchanged. Regenerated 700
public, 500 four-field, and 200 five-field leaves; all 1400 exact audits pass
with the same per-node minimum slack 0. The smoke now has two closed rational
leaves, including the corrected `(5,4)` bound `-1/4 <= -1/8`.

Files/SHA256 (lowercase): smoke
`1a0e722058e136d6629c42829e74d5242d74a3df3ef20ace0f12fd4e08c1ee49`;
public emitter
`61df6ad7fb08e177a29af90689a697a0fa653d9f327cbf4f49db4ad283c59bcf`;
four-field emitter
`94a80f85ca4b0530c823fe56f74b7a4a29b35e786f35d3839112264e99cfc950`;
five-field emitter
`9bf5fd3a5906490fe554506b06b2f18d11691ba78377ceadfd9950f1c895566c`.
Public row caps: 1409 `8772e4e0...`, 2337 `bbb2256d...`, 2341
`f0d73e7e...`, 2356 `b339b719...`, 2360 `019312d2...`, 2368
`713d7d66...`, 2370 `0a9a2656...`; four-field cap module
`6a75d16f...`; five-field cap module `d9ddf4f0...`.

Checks: all emitters exit 0; exact audits 700/700 + 500/500 + 200/200 pass with
minimum slack 0; `py_compile`, `git diff --check` pass. A bounded direct Lean
attempt failed before parsing imports because the project search path was not
lake-configured; this is **not** a syntax or kernel claim. All touched modules
remain **CI pending**.

Still unproved/missing: kernel exits, exclusion-to-radius bridge, packet
existence/`Valid`, 382 residual payloads, MPacket validity, energy and
seven-class premises.

Next: fresh serial CI starting with smoke and `1409`. If a leaf is red, capture
the full first diagnostic; if green, proceed through public/four/five-field
trees before claiming any exclusion payment.
ROOT-IMPORT REQUEST: none.

## 2026-10-31 - part 176 (current CI evidence isolated; CI pending)

`LATEST.md` run `41168580187` (source `0f022bfb`) reports `change` failures at
`FrozenCapRowCap1409Smoke.lean:25,39` and `FrozenCapRowCap1409.lean:121...`.
Those are stale: the current smoke SHA is `1a0e7220...`, current `1409` was
replaced by the part-175 `Fin.sum_univ_succ` revision SHA `9232472a...`, and
`rg 'change'` over all seven public row-cap modules plus both rescue cap
modules has no hit. A separate run `41172673380` / `7fbff386` was only
`in_progress`; it is not a result.

Current module hashes: `1409` `9232472a...`; `2337` `b860cb24...`; `2341`
`ebb04223...`; `2356` `d53fc3ee...`; `2360` `cfa89fec...`; `2368`
`340217d2...`; `2370` `c338a97c...`; four-field caps `e08f5fcd...`;
five-field caps `9c8217a8...`. Emitter hashes match part 175:
`202aba2a...`, `1619bcec...`, `203c4d84...`. `git diff --check` exits 0.

A 70 s Mathlib-probe check of `Fin.sum_univ_succ` timed out with no diagnostic;
this gives **no syntax or kernel claim**. All current modules remain **CI
pending**. Missing obligations are unchanged: cap/tree kernel exits,
exclusion-to-radius, packet existence/`Valid`, 382 payloads, MPacket validity,
energy and seven-class premises.

Next: supervisor commit and fresh serial CI. Read the first diagnostic from
source `9232472a...`; do not act on the stale `change` lines. If `1409` is
green, proceed to `2337` and the four/five-field caps before tree aggregates.
ROOT-IMPORT REQUEST: none.

## 2026-10-31 - part 177 (row dispatch to exact leaves; CI pending)

Replaced all abstract-row `norm_num [.., Fin.sum_univ_succ]` proofs in the
public, four-field, and five-field emitters with `fin_cases j` dispatch to
the corresponding already-generated closed rational leaf theorem. This
removes the sum-unfolding site that failed at current-source
`FrozenCapRowCap1409.lean:520`. Interfaces, matrices, certificates, and leaves
are unchanged. Regenerated 700 public + 500 four-field + 200 five-field rows;
all exact audits pass and per-node minimum slack remains 0.

Files/SHA256 (lowercase): frozen emitter
`eb984e88ed05357686f78100cb62e31aaf0ad4cde6c246d91c7fc68a01ba7edf`;
four emitter `aff8185962de5a78bfacad5ae6589fe0a1f6bec9ac8accb12dd952b9611f4e21`;
five emitter `92d43b54286d0a267ee212402565925a630eb70c6edd09d5bdd0b862a5444284`.
Public caps: 1409 `c27e0d06...`, 2337 `20ca0966...`, 2341 `b93339f7...`,
2356 `6b0dbb94...`, 2360 `c147be2f...`, 2368 `dfdc1444...`,
2370 `ed7a4834...`; four-field caps `1e4a25e3...`; five-field caps
`3502a5a8...`. `TARGETS.txt` is unchanged because all module names are stable.

Checks/scope: all three emitters exit 0; exact rational rechecks pass
700/700 + 500/500 + 200/200 with minimum slack 0; `py_compile`,
`git diff --check`, forbidden-token scan, and 120-column scan pass. A 90 s
Mathlib-probe import check timed out with no diagnostic; there is **no local
Lean syntax or kernel claim**. All regenerated modules are **CI pending**.

Still unproved/missing: kernel exits for all caps/trees/aggregate; exclusion
to `RemainingTerminalRadius`; packet existence/`Valid`; 382 payloads; MPacket
validity; energy and seven-class premises.

Next: fresh serial CI, smoke then `1409`; on red preserve the first current
source diagnostic. If green, continue through all seven public caps, then
four/five-field caps and trees.
ROOT-IMPORT REQUEST: none.
