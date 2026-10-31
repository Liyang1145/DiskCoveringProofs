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
## 2026-10-31 - condensed parts 165--167 (row leaves; CI pending)

Five-field certificates for `2356` and `2360` were emitted, then all public
row-cap leaves were changed to explicit `Fraction` `change` targets followed
by bare `norm_num` (700 caps); the four/five-field leaves were aligned later.
Emitter SHA256 values: public `320577b3c170d17265259f19fd1a50e47e75cc8ae86ead0e7115ba61abd3fc25`,
five-field `4be2310dd8d3a55122c9b526b939a656fc4f9999f88a4886d9d069abe3ca4bf6`.
Exact audits pass, but no local Lean syntax/kernel claim follows; bounded
probes timed out without diagnostics. A stale CI failure at `1409:132:608`
does not match the current multiline source.

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

## 2026-10-31 - condensed part 169 (four/five-field leaves aligned; CI pending)

Four-field emitter `7a7806f8...` regenerated its 500 leaves and five-field emitter
`4be2310d...` its 200 leaves; exact audits passed with minimum slack 0. Witnesses
stayed `7141cb51...`. All remained CI pending; current files were superseded by part 173.

## 2026-10-31 - part 170 (stale row-cap CI diagnostic isolated)

Compared `ops/ci/LATEST.md` (`24e434b4`, 2026-10-31T00:29:48Z) with the
part-166/169 sources. Its first row-cap failure is
`FrozenCapRowCap1409.lean:132:608: unsolved goals`, repeated at further
single-line goal sites. Current `FrozenCapRowCap1409.lean` is multiline at
that location (`row_cap_1409_0_2`, lines 129--133) and has SHA256
`a7283d64f504864abb6590e68dab8de7f187d7f6f7d3a7ca1ddf970a43e1a011`;
therefore this CI error concerns an earlier byte revision and is **not**
evidence against the current `change`/`norm_num` leaves. The smoke module
remains SHA256
`a4b3428e2526f8f488ddacc31e768fa08d0cc14fb50cc2a970ffb6060d8a985c`.

Scope: source/timestamp/hash comparison only; no new Lean run. Current smoke
and all row caps remain **CI pending**. Missing obligations are unchanged:
kernel exits, exclusion-to-radius bridge, 382 residual payloads, packet
`Valid`, MPacket validity, energy and seven-class premises.

Next: fresh serial CI must start with the smoke leaf and expose the first
diagnostic from the current SHA. Preserve that exact location before changing
any emitter; do not treat the stale `:132:608` failure as current.
ROOT-IMPORT REQUEST: none.

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

## 2026-10-31 - part 172 (row-cap `change` diagnosis and repair; CI pending)

Run `41168580187` gave exit 1 for the smoke and every row-cap module. Its first
current-source diagnostics are `FrozenCapRowCap1409Smoke.lean:25:2` and `:39:2:
'change' tactic failed, pattern`; `FrozenCapRowCap1409` then fails at every leaf
`change`. The smoke also contained a genuine arithmetic error: pair `(5,4)` is
`-1/4 <= -1/8`, not `1/2 <= 1/2`. The emitted caps themselves were correct.

Repaired all three lane emitters to prove each leaf directly with
`norm_num [rowA, y<N>, db<N>]` (and no `change`), then regenerated the seven
public modules (700 caps), the five four-field modules (500 caps), and the two
five-field modules (200 caps). Corrected the smoke's `(5,4)` bound and made both
smoke leaves use the same direct tactic. Five-field witness bytes are unchanged.

Files/SHA256 (lowercase): smoke
`f075d8b29a8410f94f0c8cedd9ff99355595396aa74ec5f6629d0f1470cf5f48`;
public emitter
`e9e11e09a2a8fa55c34e71f95594e5f772c24e6dc8be5af612f98f81075d0f6f`;
four-field emitter
`de6671ad06314a99c11929394f62a2403c7d76b18df5b3d4c86130aa140ba455`;
five-field emitter
`0c8f9aa5ccf835661088b43be083018b55fcf4995f0daa41e952e63f2eb56b89`.
Public row caps are `d3aed02a...` (1409), `f69d3ec3...` (2337),
`c2145c43...` (2341), `b5fabdd8...` (2356), `a01ebc50...` (2360),
`d82ebbcf...` (2368), `a846dbe4...` (2370); four-field row caps
`367f263b3214bfaaf1e81991d8d9582c757e8fa3856b7b6e3694f06276845767`;
five-field row caps `6e1706198d5f3385361772991a77551120d32b0675f68930cfd616c856f04ae1`.

Checks: all three emitters exit 0; exact audits pass on 700/700 public,
500/500 four-field and 200/200 five-field caps with per-node minimum slack 0;
`py_compile`, `git diff --check`, and forbidden-token scan pass. A bounded local
Mathlib probe timed out with no diagnostic, so there is **no local Lean syntax
or kernel claim**. All row-cap/tree targets and the new aggregate remain **CI
pending**.

Still unproved/missing: kernel exits for smoke, row caps, four/five-field and
public trees/aggregate; exclusion-to-`RemainingTerminalRadius` bridge; packet
existence/`Valid`; 382 residual payloads; MPacket validity; energy and
seven-class premises.

Next: fresh serial CI must rebuild the corrected smoke, then `1409`; if either is
red, capture the full first `norm_num` diagnostic (including the goal) before
changing the emitter. Exact cap audits are not kernel payments.
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

## 2026-10-31 - part 174 (row-cap interface mismatch fixed; CI pending)

Part 173's closed-rational leaf statements were not definitionally equal to the
subgoals in the generic `row_cap` interfaces, so `exact row_cap_<id>_<i>_<j>`
could not have worked even if each leaf compiled. Repaired all three emitters
without changing theorem names or cap matrices: public/five-field row lemmas
and four-field generic lemmas now prove each finite row directly with
`fin_cases ... <;> norm_num [rowA, y<N>, db<N>]`; closed-rational leaves remain
as independently checkable arithmetic but are no longer used for those exacts.
Regenerated seven public (700 leaves), four-field (500), and five-field (200)
modules. Exact audits pass 1400/1400, min slack 0 per node.

Emitter SHA256: public
`e97a484d0cdf1a61494f82c5321d1854af949a4ec4de7f44f0ac3e10f560c66c`;
four-field `e91a90b2915a65d78f83600982155ba14ae4c6e441570aca940fbaee6562e30c`;
five-field `7c1b20861a736563a1e6ecb09706cb4fe19ac482e3bd8045e0f47bbf2170e616`.
Module SHA256: 1409 `bcd85599c6d721069ca3d34ca8513ef8f8962859899ecd7508597bdcfb337bcf`;
four-field `7aeacae12ad1da54347768b0f029f5d96e12f89cabb0f854cc1eb189f8df9374`;
five-field `93d5fe0a24b25857263316221e9cfea0db593f43320eb5edf1fce73ceb2b3a09`.
Checks/scope: emitters exit 0; `py_compile`, `git diff --check`, forbidden scan
pass. Local smoke could not start because `FrozenCapRationalCore.olean` is not
built in this worktree: **no local Lean syntax/kernel claim**. CI pending.

Still unproved/missing: kernel exits for smoke/row caps/trees/aggregate;
exclusion-to-`RemainingTerminalRadius`; packet existence/`Valid`; 382 payloads;
MPacket validity; energy and seven-class premises.

Next: fresh CI must start at smoke then 1409. If direct `norm_num [rowA,y,db]`
fails, preserve full first current-SHA goal/diagnostic; do not revert to the
part-173 mismatched exact interface.
ROOT-IMPORT REQUEST: none.
