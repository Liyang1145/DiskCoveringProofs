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

## 2026-10-31 - part 175 (`Fin.sum_univ_succ` row-cap repair; CI pending)

Current-source run `41176805557` showed `FrozenCapRowCap1409Smoke` exit 0 but
`FrozenCapRowCap1409.lean:520:53` unsolved: after `fin_cases j`, `norm_num
[rowA, y_1409, db]` left the `∑ x : Fin 9` unevaluated. Added
`Fin.sum_univ_succ` to all three row-cap emitters. Theorem names, matrices,
interfaces, and leaf arithmetic are unchanged.

Emitter SHA256 (lowercase): `emit_frozen_cap_row_caps.py`
`202aba2a974d2592c830321edb7f0121d7d3fca2f8a093e41c5ebb00070d4b5a`;
`emit_four_field_row_caps.py`
`1619bcec1ec6cff60c2dd492449f7538ec7b88e2137039aa58f261e7ae30ce67`;
`emit_five_field_certificates.py`
`203c4d84f1690a8f49860f8ec2f9a3aa766adb0ccafd53ad2f562da0377cf842`.
Modules: `FrozenCapRowCap1409` `9232472a8c13e14a378d86c6a854b8437ca8e654a3c336c8f740c90ba2a34ae4`;
`FrozenCapRowCap2337` `b860cb24acc465be6ecd51fe1605ddcacdde836dc25ad29ca4a1d627aef04444`;
`FrozenCapRowCap2341` `ebb042234eb232e9bc4709116cf87891e97dd5a6df63a09074a98ce10c6b3330`;
`FrozenCapRowCap2356` `d53fc3ee3e11c8355186eea71bd7fe2a4adb02ec97775da5f183c3bd36adae87`;
`FrozenCapRowCap2360` `cfa89fec59578a971ace93cb0137c0a4712a15f73a7337384c4aeb653578f5d2`;
`FrozenCapRowCap2368` `340217d21f9d7f04c835c4e77056beb914486d32f1bd76ec1b98940e2138758c`;
`FrozenCapRowCap2370` `c338a97c3875702d7bac2471925357960853f53f4678d9fe18968e97720c9d72`;
`FrozenCapFourFieldRowCaps`
`e08f5fcda499e4cb104750235586f64ebda10f4822db49a96f06558f71ae2b29`;
`FrozenCapFiveFieldRowCaps`
`9c8217a844c3d3fb07eaf596484b4aa8f2a0d249d5c4c3eaef6f2e2d8e0d8517`.

Checks/scope: emitters exit 0; exact audits pass 700/700 + 500/500 + 200/200,
per-node minimum slack 0; `py_compile`, `git diff --check`, and forbidden scan
pass. This is exact arithmetic plus one CI-derived tactic diagnosis, not a new
kernel exit; repaired modules are **CI pending**.

Still unproved/missing: kernel exits for repaired caps and dependent trees/
aggregate; exclusion-to-`RemainingTerminalRadius`; packet existence/`Valid`;
382 payloads; MPacket validity; energy and seven-class premises.

Next: fresh serial CI must rebuild smoke (known exit 0), then `1409`; if green,
continue through all seven public caps and both aggregate cap modules. If a sum
remains, capture its full first current-SHA goal before any interface change.
ROOT-IMPORT REQUEST: none.

## 2026-10-31 - condensed part 169 (superseded by part 173)

Four/five-field leaves were regenerated with exact audits and minimum slack 0;
these bytes were superseded by part 173.
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
