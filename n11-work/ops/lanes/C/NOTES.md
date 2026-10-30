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

## Condensed history through part 131

- Exact B13 residual census is 389 ids. Seven public exclusions
  `{1409,2337,2341,2356,2360,2368,2370}` are residual and unpaid; no public
  payloads were found for the other 382 (not proof of external HOST absence).
- The wide-field family has exact checks for seven vectors, 700 row caps and
  strict `gain < T^2`; later bulk row-cap splitting was CI-red/timed out.
- Found 57 archive refinement drafts on `origin/ci/n11-build`; 15 are forbidden,
  so do not mass-import. Earlier N3040/N2965/N3440/N3589/N3623/N3633 singleton
  chains pass integer tree audits (root 491520, terminal children), not packet
  validity. Membership covers 57 Next1182 components; B10/remaining-210
  absence still rests on kernel `decide`. All such chains are CI pending unless
  LATEST says otherwise. Unproved throughout: packet/kernel validity, positive
  packet/no-cell and exclusion-to-radius bridges, energy and seven-class premises.
## 2026-10-30 - parts 132-136, condensed

- Restored and audited singleton chains N2337/N2341/N3040/N2965/N3440/N3589/
  N3623/N3633; seven-certificate aggregate and Main were subsequently CI green.
- N2337 uses a bounded 25-block Next505 absence check. Static tree audits cover
  exact integers only, never MPacket validity or kernel credit.
- Remaining obligations stayed: 378 ids, packet/no-cell and exclusion-to-radius
  bridges, energy and seven-class premises.

## Parts 137-139, condensed (N3792/N3853/Eleven)

- N3792 and N3853 were restored from clean archive bytes; each has a singleton
  `EnergyRefine`, B13 wrapper, and conditional Main. Exact tree audits passed
  100/100 root and 200/200 splits, with roots `(false,2,6,475136,1,2)` and
  `(false,1,6,516096,1,2)`, terminal children, forbidden-token/diff checks 0,
  and both ids absent from Next1182. Module SHA256: N3792
  `66e978317d4c0d7caa4f26402c532de61d7746e34c9a9ac544751cab656f3d6d`;
  N3853 `d2cc6ec701832c657d5be545e25eb7158fd083ef9bb90b47d491581ea4390e7e`.
- `EnergyTerminalBatchB13RefineEleven` composes Eight plus 3777/3792/3853 and
  declares conditional `paid_count = 2008`; module SHA256
  `5121a39cdf36a06c853233256934224f70476e640f4778c316ff803f2d46da39`.
  These static results are not kernel credit: all 3792/3853/Eleven targets are
  **CI pending**. Missing: 378 residual ids, MPacket validity, packet/no-cell
  and exclusion-to-radius bridges, energy and seven-class premises.

## Parts 140-144, condensed

- Runs before `41098508743` proved the seven singleton wrappers plus Seven
  green. Eight failed at `simp made no progress`; the fix calls
  `EnergyRefineN2337.new_radius` directly without substitution. Seven/Eight/
  Eleven were also corrected for redundant `norm_num`. Run `41098508743` later
  proved Eight, Eleven, and their Mains green.

## 2026-10-30 - part 146 (N37 restored as source-only CI target)

Re-fetched the archive N37 source with `git show`; SHA256 is
`7a0137826c2ea9c5975ee9d3b19952e409e86551b93262778933c3752240d0ac`, matching
the audited candidate. Re-ran `audit_archive_refine_tree.py`: 7 nodes, terminal
`{2,4,5,6}`, 100/100 root-scale entries, 600/600 split entries, zero
mismatches, exit 0. Scope is exact integer tree data only, not MPacket,
module-compilation, axiom, or kernel credit.

Preserved those exact bytes as new
`n11-work/lean/N11Formalization/EnergyRefineN0037.lean`; added only
`N11Formalization.EnergyRefineN0037` to TARGETS (46 distinct non-comment
targets). No wrapper, paid count, or residual reduction was added. The generic
restore helper had used unpadded `N37` for both its namespace guard and output
path even though the archive module is `N0037`; both now use `{node:04d}`. A
rerun reproduces SHA256 `7a013782...40d0ac` and then correctly refuses to
overwrite the preserved module.

The Eight patch from part 144 is still **CI pending**, not green. A local
Mathlib union-pattern probe timed out at 90/120 seconds (exit 124), so it gives
no evidence and is not cited. `git diff --check` passes; forbidden-token scan
over N37 has zero hits.

Still missing: Eight/Eleven kernel exits; N37 module/axiom exit and MPacket
validity; N37 wrapper/aggregate integration; 378 residual ids; packet/no-cell
and exclusion-to-radius bridges; energy and seven-class premises. Next: read
fresh CI's first Eight error (if any), then N0037's first error; do not emit the
N37 wrapper until Eight/EightMain are exit 0 and N0037 passes. ROOT-IMPORT
REQUEST: none.

## 2026-10-30 - part 147 (Eight/Eleven CI green; N0037 still pending)

Downloaded CI run `41098508743` for commit
`1b2fa7a833e191c65615ed136d5799add6fb6009`. It supersedes the stale
`ops/ci/LATEST.md` run `41082175973` for this lane:
`EnergyTerminalBatchB13RefineEight`, `RefineEightMain`,
`EnergyTerminalBatchB13RefineEleven`, and `RefineElevenMain` all exit 0.
The logs show `RefineEleven.remaining_of` and `RefineElevenMain`'s main theorem
depend only on `[propext, Classical.choice, Quot.sound]`. Thus the conditional
11-certificate aggregate and its `paid_count = 2008` theorem are CI green.
This is not root-reachable credit: no root import was changed, and the
`RemainingTerminalRadius` premise remains unpaid.

`EnergyRefineN0037` was added to lane C TARGETS only after that run, so it was
not built there. It remains **CI pending**, not green. Its preserved source
SHA256 is `7a0137826c2ea9c5975ee9d3b19952e409e86551b93262778933c3752240d0ac`;
the exact-integer tree audit covers 7 nodes, terminal `{2,4,5,6}`, 100/100
root-scale and 600/600 split entries, with zero mismatches. That audit is data
scope only; it does not establish MPacket validity, compilation, or kernel
credit. A final audit replay at that hash again passed. No N0037 wrapper was
emitted. Final static checks: 46/46 TARGETS distinct and resolvable;
forbidden-token scan over N0037 empty; `git diff --check` exit 0.

Still unproved/missing: N0037 module/axiom check and wrapper integration; 378
residual ids after the 11 conditional aggregate plus N0037 if it proves valid;
MPacket validity for N0037; packet/no-cell and exclusion-to-radius bridges;
energy and seven-class premises. Next: fresh CI must show
`N11Formalization.EnergyRefineN0037` exit 0 at the preserved hash. Only then
emit its singleton wrapper/Main from the 3853 template and request the next
kernel check. ROOT-IMPORT REQUEST: none.

## 2026-10-30 - part 148 (N0037 wrapper and twelve-certificate aggregate drafted)

Updated `emit_refine_singleton.py` so padded module stems (`0037`) map to
unpadded Lean ids (`37`), then generated `EnergyTerminalBatchB13Refine0037` and
its Main from the CI-green 2965 template. Added
`EnergyTerminalBatchB13RefineTwelve`/`Main`: paid set =
`RefineEleven.paidIDs ∪ EnergyRefineN0037.newIDs`, conditional
`paid_count = 2009`, and `remaining_of` (`Twelve.Remaining -> B13.Remaining`),
dispatching N0037 and all eleven prior additions before the refined premise.
This aggregates rather than duplicating the base singleton count.

SHA256: N0037 source `7a0137826c2ea9c5975ee9d3b19952e409e86551b93262778933c3752240d0ac`;
Refine0037 `934096ba33053676f1f9e4e5a3f78f6a464c25bc3e037e4e5c24ec945d6137f2`;
Main `4ebbe1ff62b2b6a12fa5afab0813e3ff604dd8e201839e66ef2ab9cd2f90ad55`;
Twelve `1479d68d7db45c6631e0e8b856e9caa9baa3a2e8e8f1e6dbe5c74548173471b8`;
TwelveMain `665ba8116cc6f756f589f24abdd9aa830651b5ffcd406729d8787b1fd58b0086`.

Checks executed: tree audit on N0037 exit 0 (7 nodes, terminal `{2,4,5,6}`,
100/100 root-scale, 600/600 split, zero mismatches; integer data only);
rerun report byte-identical to `energy-refine-n0037-tree-audit.json` SHA256
`85822ecbafac3cd9a87632e72f55764b30bd1b864663b13aaf7ed81aa292d1e9`;
`git diff --check` 0; forbidden-token scan over the five modules 0; 50/50
non-comment TARGETS distinct and resolvable. No Lean build or axiom report was
run locally; a 60-second generic Mathlib singleton-card probe timed out (exit
124), so the aggregate uses the proven template `simp` singleton lemma instead.
A source census found 12 distinct ids (37 plus the prior 11), with no overlap;
this is text/data scope only.
All five new targets are **CI pending**; no residual reduction or
credit is claimed yet.

Still unproved/missing: kernel/axiom exits for N0037, Refine0037/Main, and
Twelve/Main; 377 residual ids conditional on those exits; N0037 MPacket validity;
packet/no-cell and exclusion-to-radius bridges; energy and seven-class premises.
Next: fresh CI must pass N0037 first, then the wrapper and Twelve pair; inspect
their first exact errors and do not claim 377 before all exits are 0.
ROOT-IMPORT REQUEST: none.

## 2026-10-30 - part 151 (three compact residual refinements restored)
Latest CI (`1b2fa7a8`, run 41098508743) is green for `RefineEleven` and its
Main, plus the previously listed energy chain; it contains no N0037/Twelve/
N3112 exits, so those remain **CI pending**. Restored three additional clean
archive refinements N3116/N3431/N3573 (no forbidden tokens), each 5 nodes with
terminal sets `{1,3,4}`, `{1,3,4}`, `{2,3,4}`. Exact integer audits passed
100/100 root-scale entries and 400/400 split entries each; this is tree-data
scope only, not MPacket validity or kernel credit.

SHA256 sources: N3116 `70053e95b07b481d3c08aa02ef9d857c11d896118c773595af87756e5d034421`;
N3431 `3aac08483d7e2bd0978901e36b4a75ef7aeae6fc289e3fd8a5ffead69c85c685`;
N3573 `37c6090a9985ccf2db1100c42ec941341dbcb7c60c5dc2a207475757bc7b5044`.
Emitted conditional `Refine3116`, `Refine3431`, `Refine3573` and their Mains
from the green 2965 template (`paid_count = 1998`, no new aggregate). Six new
wrapped targets plus three source targets were added, all **CI pending**.
Checks: forbidden-token scan over all nine files 0; `git diff --check` 0;
62/62 non-comment TARGETS distinct and resolvable. No Lean build/axiom report
was run locally.

Still unproved/missing: kernel exits for N0037/Twelve/N3112/N3116/N3431/N3573
chains; 373 residual ids conditional on all exits; MPacket validity; packet/
no-cell and exclusion-to-radius bridges; energy and seven-class premises.
Next: fresh CI must isolate the first red target after `EnergyRefineN0037`;
do not extend the paid aggregate until each source and wrapper exits 0.
ROOT-IMPORT REQUEST: none.

## 2026-10-30 - parts 149-151, condensed
N3112/N3116/N3431/N3573 source trees and conditional wrappers were restored and
audited (static exact-integer scope); N0037/Twelve/N3112/N3116/N3431/N3573
kernel exits remain CI pending. Part 150 fixed a stale Eight diagnostic and
reordered N0037/Twelve before Eleven. Part 151's three refinements each passed
100/100 root and 400/400 split checks.

## 2026-10-30 - parts 152-155, condensed
The old all-pairs row caps and their decomposed 100-leaf versions were CI red;
explicit `Fin` annotations (part 154) did not cure the failures. Generator
checked 700/700 exact-rational caps with min slack 0; DBM SHA256 begins
`BD4E71CB`, and generated module hashes are recorded in git history. Static
checks passed but exact arithmetic is not kernel credit. Part-154 bytes are
superseded by the CI result in part 156; no row-cap credit is claimed.

## 2026-10-30 - part 156 (CI red: first row-cap leaf still unresolved)
Run `41115384387` (`9445f2b2`) completed **red**. The part-154 rewrites did not
fix the row caps: 1409/2337/2341/2360/2368/2370 all fail at declaration
`FrozenCapRowCap*.lean:34:53` (`unsolved goals`), while 2356 hits the 200000
heartbeat limit at `:33:0`. Thus explicit `Fin` annotations were not the cause.
CI's captured log gives only the declaration position, not the residual goal.
Exact source hashes remain those recorded in part 154; I did not regenerate
under a new unverified tactic. A minimal Mathlib probe reproducing the first
summand timed out at 90s during imports (exit 124), so it is inconclusive and
no local Lean claim is made. FrozenCapRationalCore itself is CI green (`0`).

Interpretation/next concrete step: isolate a one-leaf module importing
`FrozenCapRationalCore` plus `Mathlib.Tactic.NormNum`, containing only
`rowA`, one `y_1409` literal, and the first cap; add only that probe to
TARGETS. If it is red, test simplification of `Fin.val`/`if` before changing
all 700 leaves; if green, difference the failing declaration's exact term.
Do not claim any row-cap/kernel credit or reduce the residual. Other missing
obligations unchanged: public-tree assembly, residual-chain exits, MPacket
validity, packet/no-cell and exclusion-to-radius bridges, energy/seven-class.
ROOT-IMPORT REQUEST: none.
