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

## Condensed history through part 119

- Exact B13 residual census is 389 ids. Public exclusion payloads cover
  `{1409,2337,2341,2356,2360,2368,2370}`; 382 HOST records remain absent.
  Seven public exclusions are formally residual and unpaid, not radius proofs.
- The frozen-cap wide-field family gives exact rational checks for seven
  probability vectors, 700 ordered row caps, and strict `gain < T^2` margins.
  Later row-cap splitting remained CI-red from heartbeat limits; stop that family.
- A scan of 702 public/restored JSON files (51,466,284 B, plus two oversized C450
  files) found zero payloads for the other 382 ids. This is not proof of external
  HOST absence.
- Found 57 distinct residual refinement drafts on `origin/ci/n11-build`
  (6,949,370 B; 15 use forbidden `maxHeartbeats 0`). Do not mass-import them.
- Run `41027178023` (commit `34b14918`) is green for
  `Paid16MatrixCellCertificate`, `EnergyRefineN2341`, all B13 prerequisites,
  and B13. Its old B13Main was red solely because it imported the broken
  residual-census path; the current B13Main has that import removed.
- Restored exact archive bytes for `EnergyRefineN3040`, N2965, N3440, N3589,
  N3623, and N3633. Each passes 100 root-scale and 200 split checks, with root
  `(terminal=false, i=1, j=6, m=491520, left=1, right=2)` and terminal children.
  These are static/data checks only; their Lean modules and packets are CI pending.
- N3040 SHA256 is
  `7fcd5e3b8d528dfd3602a1f84709ca66c54e78de198116caec28d8b47ac4e057`.

## Earlier singleton chains, parts 120-124 (condensed)

- Wrapper/main pairs were emitted for N3040, N2965, N3440, and N3589 from the
  audited N2965 template; `emit_refine_singleton.py` makes 3589/3623/3633
  reproducible. Their stored tree audits cover integer tree data only:
  N3440/N3589 report 100/100 root-scale and 200/200 split checks.
- The membership audit covers 57 Next1182 components (union 1182, largest 21,
  `S07.ids55`) and finds none of 3040/3440/3589/3623/3633. Absence from
  B10/remaining-210 still rests on kernel `decide`; Next505 uses the audited
  bound. All these chains remain **CI pending** unless LATEST proves otherwise.
- Then-unproved: packet/kernel validity, residual positive-packet/no-cell
  bridges, exclusion-to-radius bridges, and the energy/seven-class premises.

## Earlier N3623/combined/CI history, parts 125-131 (condensed)

- N3623 wrapper/main emitted with exact data audit; all seven singleton chains and the combined seven-certificate pair remained CI pending. The old residual-census import was removed after a CI type error. These older details are superseded by the later per-node entries below.
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

## 2026-10-30 - part 149 (N3112 drafted)

Restored/audited N3112 (5 nodes; terminal `{1,3,4}`; 100/100 root, 400/400
split, data scope only) and emitted conditional `Refine3112`/Main, paid count
1998. All **CI pending**. Source `1b76594f3d3102f3e5c2902bfd19521bbb185f37cdbf6f278dfb77d6cf00318c`.

## 2026-10-30 - part 150 (stale Eight diagnosis)

Old CI error `RefineEight.lean:63:50` was already fixed in worktree; no kernel
claim. Reordered N0037/Twelve before Eleven in `TARGETS.txt`.

## 2026-10-30 - part 152 (row-cap red cause fixed in generator)

Pulled CI run `41098508743` logs. `FrozenCapPublicExcludedTree` exited 1 because
all seven `FrozenCapRowCap*` dependencies failed at their `row_cap` proof:
transparent `norm_num` left goals of form `... ≤ ↑(dbmVal 0 ⟨j, _⟩) / 4096`
unreduced (2356 also hit 200000 heartbeats). Patched
`n11-work/ops/lanes/C/emit_frozen_cap_row_caps.py` to include `dbmVal` in the
unfold set, then regenerated the seven modules.

Checks: generator exact-audited 700/700 ordered caps against the frozen DBM
(`BD4E71CB…A8ED5`), minimum slack 0, exit 0; static exclusion audit exit 0
(closure 460, seven exact theorem ids, no forbidden imports/tokens);
`git diff --check` exit 0. This is data/static scope only. The corrected row-cap
proofs, exclusion theorem and axiom reports remain **CI pending**.
Row-cap SHA256: 1409 `6778EACA…D2B5`, 2337 `FBBA6318…FDC5`, 2341
`B445A626…A3C6`, 2356 `2905ACF6…F85D`, 2360 `C9981064…DCB1`, 2368
`3CF9BDD1…3C60`, 2370 `61ACA6E6…22D6`.
Still missing: kernel exits for this chain; N0037/Twelve/N3112/N3116/N3431/
N3573 chains; 373 residual ids conditional on exits; MPacket validity;
packet/no-cell and exclusion-to-radius bridges; energy and seven-class premises.
Next: fresh CI must confirm all seven row caps and then
`FrozenCapPublicExcludedTree`; if green, inspect the first pending singleton
error rather than extending the paid aggregate. ROOT-IMPORT REQUEST: none.
