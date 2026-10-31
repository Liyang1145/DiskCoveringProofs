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

## 2026-10-31 - part 169 (four/five-field leaves aligned; CI pending)

Extended the part-166 exact-rational leaf pattern to the four- and five-field
row-cap emitters. Each leaf now `change`s to the computed `Fraction` LHS and
RHS, then runs bare `norm_num`; no `rowA` vector lookup or 100-clause `db`
table enters leaf arithmetic. Regenerated five four-field nodes (500 caps) and
the two five-field nodes (200 caps); exact weights, slacks and DBM hash are
unchanged. This is proof engineering only, not a residual payment.

Files/SHA256 (lowercase): four-field emitter
`7a7806f8e2c060ac61eecab6a1a18edc52abd0cb59f7b81b7fdf5d87065ce201`;
four-field caps `ec626ad4dcbddafd223dee31b028184715aa9388d347992e3bcc1c02e6ad6336`;
five-field emitter
`4be2310dd8d3a55122c9b526b939a656fc4f9999f88a4886d9d069abe3ca4bf6`;
five-field caps `728c84e73187597786016f5807988b921692cee3c7a5a82594d97a09248ce412`.
Five-field witnesses stayed byte-identical
`7141cb51f0f4980f523ddde7d12a9a84d487db777a5687dd2f5a153375d74fbb`.

Checks: both emitters exit 0; 500/500 four-field and 200/200 five-field exact
caps pass with per-node minimum slack 0; `py_compile`, `git diff --check`, and
the stale-tactic scan exit 0. No local Lean run was possible, so all row-cap
modules remain **CI pending**; the smoke/public part-166 targets also remain
pending because `LATEST.md` is still at `24e434b4`.

Still unproved/missing: kernel exits for all row caps, public/four/five-field
excluded trees and aggregate; bridges to `RemainingTerminalRadius`; packet
existence/`Valid`; 382 absent payloads; MPacket validity; energy and
seven-class premises. Row caps alone pay neither `x/2386` nor `0/7`.

Next: commit this worktree for fresh serial CI. Require smoke then `1409` exit
0 before interpreting the four/five-field build. If a leaf fails, preserve the
first source diagnostic; the exact 700/700 audit is not a kernel claim.
ROOT-IMPORT REQUEST: none.

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
