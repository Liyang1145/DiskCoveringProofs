EXPERT (2026-10-30):
- CI-green lane-C modules: `Paid16MatrixCellCertificate`, `EnergyRefineN2341`,
  `FrozenCapRationalCore`, `PaidCellCertificateM`, `PaidCellCertificateMCap`,
  `FrozenCapWideFieldWitnesses`, `Paid16GeneralNext1182`,
  `EnergyTerminalBatchB13Next505Bounds`, `EnergyTerminalBatchB13DescentBounds`,
  and `EnergyTerminalBatchB13`.
- Highest leverage: green B13 paid-set refinements for N2341/N3040 plus
  conditional main consumers. A payment still requires the wrapper and consumer
  to be CI-green; a split certificate or cardinality alone is not payment.
- Do not re-import the optional residual census C02 into B13Main. It was red at
  `34b14918` with `Expected type must not contain free variables`.

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
## 2026-10-30 - part 132 (N2337 archive restoration, condensed)

- Restored clean archive bytes for N2337 (28,421 B), emitted its singleton B13
  wrapper/main, and extended `emit_refine_singleton.py`; this is a new residual
  refinement, not the public frozen-cap exclusion for 2337.
- Exact integer tree audit: 100/100 root-scale, 200/200 split; root
  `(false,0,5,393216,1,2)`, both children terminal; 2337 is in no Next1182 part.
- Original module SHA256: EnergyRefine
  `4b65533ffc8e2206f1b9c548b547bd050be4cfdd2fa2d3f624bbb2b5b693117e`;
  wrapper `f142268823a18da5f1073fb8d749c71417e760b9fac77ce3b3f5da9461424c84`;
  Main `b28e28cb6215cff67a158fb78b11f9e0b0f5ea4af45726748d7f785ea26a6e0f`;
  tree audit `56be7cacb6e4729b0d726675070ddfe11e9b9812a5b5721f6eebe302da4802fb`.
- Those static checks were not kernel credit; see part 142 for the later exact
  CI failure and its fixed source hash.

## Earlier CI diagnostics, parts 134-135 (condensed)

Run `41050329106` (`d70898ab`) predates the local N2337/Seven/Eight work and
dies with exit 137/OOM in unrelated `SharedMomentConcreteSwitchBatch`, so it
gives no lane-C verdict. N2337 remained structurally equivalent to green N2341
and its exact static/tree audits passed; emitter hashes were unchanged. All
those chains remained **CI pending**, not credited. ROOT-IMPORT REQUEST: none.

## 2026-10-30 - part 136 (N3777 archive restoration)

Did: restored the next-smallest clean unrecovered archive certificate (`N3777`,
28,971 B), extended the deterministic singleton emitter for 3777, and emitted
the wrapper/main pair. The exact integer tree audit passes; this is a new
residual refinement candidate, not a paid theorem.

Files / SHA256 (lowercase):
- `n11-work/lean/N11Formalization/EnergyRefineN3777.lean`
  `bc092a78a80b39eb8a01b76a6db6850dcd28ac057497efeda47cfbd8046e4380`.
- `n11-work/lean/N11Formalization/EnergyTerminalBatchB13Refine3777.lean`
  `e555a979d62fa232dbda250a571be9d928a8d6b767093dafbdde22321fb22e8a`.
- `n11-work/lean/N11Formalization/EnergyTerminalBatchB13Refine3777Main.lean`
  `fa103630e96716420845441f65cfe9e1f279ba0e2cd69ca9ac4f198ad6d2335c`.
- `n11-work/ops/lanes/C/energy-refine-n3777-tree-audit.json`
  `001d0e26771c50cc53a98d42b23cbc9dd12e8585444c4b41a2c6791eb6460a55`.
- `n11-work/ops/lanes/C/emit_refine_singleton.py`
  `965268ab772e07b02df3e9a279c443473957727e0bcddde2be18e8c0f059a438`.
- `n11-work/ops/lanes/C/TARGETS.txt`
  `9efd4edd6ba2131c2f3f1198c8d3afc8557aadf528ccaa4837a6cd2ca28c3dac`.

Checks (exact scope): audit passed 100/100 root-scale entries and 200/200 split
inequalities, root `(false,2,6,532480,1,2)`, both children terminal; integer
tree data only. Forbidden-token scan and `git diff --check` exited 0. Latest CI
is still blocked upstream by OOM before lane C; the three 3777 targets are
**CI pending**, so no kernel/axiom credit exists.

Still unproved/missing: CI exits/axioms and MPacket validity for N3777 (and all
earlier pending chains); 321 residual certificate/data ids after eight
candidates; packet/no-cell and exclusion-to-radius bridges; energy and
seven-class premises.

Next: inspect the first N3777 kernel error when CI reaches lane C; if green,
add 3777 to the combined refinement and update to eight ids / 2005 paid.
ROOT-IMPORT REQUEST: none.

## 2026-10-30 - part 139 (eleven-certificate combined consumer)

Did: built one conditional integration above the existing Eight refinement
(Seven + 2337) and the 3777/3792/3853 singletons. It removes all eleven ids
from the B13 residual premise and states `paid_count = 1997 + 11 = 2008`; the
paired Main consumer transfers this refined premise to the unchanged
seven-class interface. No mathematical premise was replaced by a cached count.

Files / SHA256 (lowercase):
- `n11-work/lean/N11Formalization/EnergyTerminalBatchB13RefineEleven.lean`
  `5121a39cdf36a06c853233256934224f70476e640f4778c316ff803f2d46da39`.
- `n11-work/lean/N11Formalization/EnergyTerminalBatchB13RefineElevenMain.lean`
  `5684672b1dbbe45894f162097d5b149285464d11eac0692dbaea1c9b432319f2`.
- `n11-work/ops/lanes/C/TARGETS.txt`
  `1da47763475e4b5df79912617d375ec7a4a9fcad63d7ee754adbe0f71982f316`.

Checks (exact scope): forbidden-token scan over both new modules found no
previously listed forbidden token; `git diff --check` exited 0; TARGETS has 45
non-comment lines, all distinct, with Eleven and ElevenMain first. No project
olean was available locally; the bounded `lake env lean` attempt did not reach
the module (dependency checkout error), so neither module has a kernel/axiom
verdict. Both targets are **CI pending**, and the combined count is uncredited.

Still unproved/missing: kernel exit/axiom status for Eleven and its dependencies
(notably 2337/3777/3792/3853); 378 residual certificate/data ids after eleven
candidates; packet/no-cell and exclusion-to-radius bridges; energy and
seven-class premises.

Next: read the first CI error in `EnergyTerminalBatchB13RefineEleven`; if the
combined module is green, focus on the first failing singleton dependency and
then the residual 378 census. ROOT-IMPORT REQUEST: none.

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

## 2026-10-30 - part 144 (stale Seven error isolated)

Re-read `ops/ci/LATEST.md`: its completed green run is `96ed4912`; the newer
`41065332260` entry is only `in_progress`, so the displayed Seven/SharedMoment
errors are not a current completed verdict. The old Seven diagnostics cite
`subst` failures and a line-64 `No goals to be solved`; the current source has
neither `subst` nor the extra `norm_num`, and a forbidden-token grep over Seven,
Eight, and Eleven returned zero hits. `git diff --check` exited 0. Current SHA256:
Seven `2446c7f843a93160e711042532a8ffd1fca5475bd9c8154d3ae0ff4c46e26ff1`;
Eight `ca24b4217b31949108365bd6bc148c393a813130b668de1aad753209da3ea2dc`;
Eleven `8bc3459f021c6afc4c01ea5ff587cb0c1c9dff77c19118b1474d3a7fea4d4017`.
These are static checks only; none is kernel credit, and Seven/Eight/Eleven remain
**CI pending**. Unproved remains: 378 residual ids, kernel exits for the aggregate
chain, MPacket validity, packet/no-cell and exclusion-to-radius bridges, and the
energy/seven-class premises.

Next concrete step: require the supervisor's fresh completed run for the current
hashes; read the first error among Seven, SevenMain, Eight, EightMain, Eleven,
ElevenMain and fix only that error. Do not add ids until this aggregate chain is
CI green. ROOT-IMPORT REQUEST: none.
