EXPERT (2026-10-30):
- Nine singleton wrappers are CI-green (N2341/N3040/N2965/N3440/N3589/N3623/N3633/N3777/N3792), but move no aggregate count.
- `RefineSeven`/`Main` and `RefineEight`/`Main` are red on proof plumbing, not data; fix the membership dispatcher first, do not mine another N file.
- Prefer `Finset.univ.biUnion parts` with `parts : Fin 9 -> Finset (Fin 5011)` and a single `mem_new : n ∈ newIDs ↔ n = ...`; dispatch with `rw [h]`, not `subst`.
- Prove `new_count = 9` via `Finset.card_biUnion` plus concrete pairwise `decide +kernel` facts, then `remaining_of` and one aggregate Main.
- Fix N2337 line 240 separately (`norm_num at hlt` or `(2337 : Fin 5011).val = 2337 := rfl`); add it only after wrapper CI is green.
- A singleton `paid_count` is not the B13 count; only an aggregate consumer with `remaining_of` can narrow 389.
- Do not claim 2004/2006/2007 or root-reachable credit before the aggregate and root/build scope are CI-green.

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

## Earlier aggregate fixes, parts 140-142 (condensed)

- Run `41065332260` (`ede0d1c8`) was green for N3777/3792 wrappers/mains and
  N2337 data, but red for `Refine2337`, Seven, and Eight. 2337's coarse
  `Next505 n.val < 2565` could not prove absence; the fix checks all 25 bounded
  literal blocks and dispatches `exact not_next505 h505`.
- Seven now destructures the left-nested union and dispatches directly to each
  singleton's `new_terminal`, `new_radius`, and `new_disjoint_old`; no invalid
  substitution is used. Fresh SHA256: Seven `a9da8012...`, Eight `869ab92d...`,
  Eleven `49fe7601...`, 2337 wrapper `e401c8ad...`.
- These proof edits had only static checks (`git diff --check`, forbidden-token
  scan) and remained **CI pending**. Missing: kernel/axiom exits, 378 residual
  ids, MPacket validity, packet/no-cell and exclusion/radius bridges, energy and
  seven-class premises.

## 2026-10-30 - part 143 (redundant `norm_num` removed)

The post-fix run still reported `RefineSeven.lean:64:2: No goals to be solved`.
The `rw` chain already closes `paid_count`; Seven, Eight, and Eleven each had an
extra `norm_num`. Removed that tactic from all three, matching the green
singleton wrappers.

File / SHA256:
- `EnergyTerminalBatchB13RefineSeven.lean`
  `2446c7f843a93160e711042532a8ffd1fca5475bd9c8154d3ae0ff4c46e26ff1`.
- `EnergyTerminalBatchB13RefineEight.lean`
  `ca24b4217b31949108365bd6bc148c393a813130b668de1aad753209da3ea2dc`.
- `EnergyTerminalBatchB13RefineEleven.lean`
  `8bc3459f021c6afc4c01ea5ff587cb0c1c9dff77c19118b1474d3a7fea4d4017`.

Checks (static scope only, not kernel): no `subst`/`rfl`/`norm_num` remain in
those three files; forbidden-token scan found zero hits; `git diff --check`
exits 0; all 45 non-comment TARGETS are distinct and map to existing sources.
All three modules remain **CI pending**; no credit is claimed.

Still unproved/missing: kernel/axiom exits for Seven/Eight/Eleven and the
CI-pending 2337/3777/3792/3853 chains; 378 residual certificate/data ids;
MPacket validity; packet/no-cell and exclusion-to-radius bridges; energy and
seven-class premises.

Next: after push, read the first fresh exit among Seven, SevenMain, Eight,
EightMain, Eleven, and ElevenMain; fix that exact error before adding ids.
ROOT-IMPORT REQUEST: none.

## 2026-10-30 - part 144 (fresh CI isolates and fixes Eight)

Downloaded artifact `n11-build-41082175973` for HEAD `40d03ae5`: Seven and
SevenMain, 2337 and its Main, 3777/3792/3853 and their Mains are all exit 0
(kernel/axiom scope for those named targets). Eight and EightMain are exit 1;
Eleven and ElevenMain inherit that failure. The exact first error is
`EnergyTerminalBatchB13RefineEight.lean:63:50: simp made no progress`, from
rewriting `n` to the literal 2337 inside `hc`.

Patched that branch to call `EnergyRefineN2337.new_radius n hn ... hc ...`
directly, using the generic membership theorem with no rewrite/substitution.
No other file changed. New SHA256 for Eight is
`3b8f66f009552523d5ff5b17607afe11c807ceb2efcfbdf6bce07fa309f0430c`.
Checks are static only: `git diff --check` exit 0; forbidden-token scan over the
file has zero hits; all 45 non-comment TARGETS remain distinct and present.
The patch is **CI pending**; Eight/Eleven currently earn no new aggregate credit.

Still unproved/missing: kernel exits for patched Eight/Eleven, 378 residual ids,
MPacket validity, packet/no-cell and exclusion-to-radius bridges, energy and
seven-class premises. Next: fresh CI must prove Eight/EightMain then
Eleven/ElevenMain green at this hash; inspect the first exact error otherwise.
ROOT-IMPORT REQUEST: none.

## 2026-10-30 - part 145 (Eight patch checked; N37 next candidate)

Confirmed the part-144 Eight dispatcher call matches
`EnergyRefineN2337.new_radius` parameter-for-parameter; old error at line 63 was
the failed literal rewrite. Static checks only: SHA256
`3b8f66f...f0430c`, `git diff --check` 0, forbidden-token scan 0, 45 distinct
TARGETS present. Eight/Eleven remain **CI pending**; no credit claimed.

Added `audit_archive_refine_tree.py` (SHA256 `f1633b18...320b08`), a reusable
exact-integer tree auditor. It reproduces N2341 (100/100 scale, 200/200 split).
Applied to clean archive candidate N37 source SHA256 `7a013782...40d0ac`:
7 nodes, 4 terminal, 100/100 scale, 600/600 split, zero mismatches. Report
`energy-refine-n0037-tree-audit.json` SHA256 `85822ecb...92d1e9`. Scope is tree
data only; no MPacket/Lean/kernel check. N37 source is still in `/tmp`, not the
tree, and no wrapper/credit was added.

Missing: Eight/Eleven kernel exits; N37 MPacket and kernel validity; 378 residual
ids; packet/no-cell and exclusion-to-radius bridges; energy/seven-class premises.
Next: once Eight/Eleven are CI green, restore N37 and run its 8 `decide +kernel`
checks through CI before emitting a singleton wrapper. ROOT-IMPORT REQUEST: none.
