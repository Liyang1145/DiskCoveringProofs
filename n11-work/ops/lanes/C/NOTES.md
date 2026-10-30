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
## 2026-10-30 - part 132 (N2337 archive restoration)

Did: added `restore_archive_energy_refine.py`, restored the smallest clean
unrecovered archive candidate (`N2337`, 28,421 B, no forbidden token), extended
`emit_refine_singleton.py`, and generated the singleton B13 wrapper/main pair.
This is a new residual refinement, not the public frozen-cap exclusion for 2337.

Files / SHA256 (lowercase):
- `n11-work/lean/N11Formalization/EnergyRefineN2337.lean`
  `4b65533ffc8e2206f1b9c548b547bd050be4cfdd2fa2d3f624bbb2b5b693117e`.
- `n11-work/lean/N11Formalization/EnergyTerminalBatchB13Refine2337.lean`
  `f142268823a18da5f1073fb8d749c71417e760b9fac77ce3b3f5da9461424c84`.
- `n11-work/lean/N11Formalization/EnergyTerminalBatchB13Refine2337Main.lean`
  `b28e28cb6215cff67a158fb78b11f9e0b0f5ea4af45726748d7f785ea26a6e0f`.
- `n11-work/ops/lanes/C/energy-refine-n2337-tree-audit.json`
  `56be7cacb6e4729b0d726675070ddfe11e9b9812a5b5721f6eebe302da4802fb`.
- `n11-work/ops/lanes/C/TARGETS.txt`
  `d1a2e959643a78993de48926b370be8ba3f8b64b35e66cb6be47ee8683ece8c7`.
- `n11-work/ops/lanes/C/restore_archive_energy_refine.py`
  `3987245dbf4dd53813fc0d1e801e9784e437ba3d108dabf0cc54e097d5449a0b`.

Checks (exact scope): exact integer tree audit passed 100/100 root-scale and
200/200 split checks, root `(false,0,5,393216,1,2)`, both children terminal;
57-component Next1182 audit has union 1182 and 2337 in no component; forbidden
token scan, `git diff --check`, and generator execution exited 0. No local Lean
kernel/axiom result: all three new targets are **CI pending**, so no credit.

Still unproved/missing: those target exits/axioms and MPacket validity for 2337;
the five earlier pending targets; 322 residual data ids; packet/no-cell and
exclusion-to-radius bridges; energy and seven-class premises.

Next: inspect the next artifact beginning with `EnergyRefineN2337`, then its
wrapper/main; fix only the first kernel error. After green, add 2337 to the
combined refinement and update the paid/count proofs. ROOT-IMPORT REQUEST: none.

## 2026-10-30 - part 134 (N2337 pre-CI diagnosis)

Did: checked `LATEST.md` and downloaded run `41050329106` logs. That run is at
`d70898ab`, predating the local N2337/Seven/Eight work, so it cannot diagnose
those modules. Compared N2337 with CI-green N2341: proof/declaration structure
is line-for-line equivalent after replacing node data; both use the same
refinement consumer and packet checks. Rechecked N2337 exact tree audit:
100/100 root-scale entries and 200/200 split entries, children terminal. The
forbidden-token scan and `git diff --check` exit 0. This is data/static scope,
not Lean kernel credit.

Unproved: N2337 `MValid pk*`, all CI exits/axioms for N2337, Seven, Eight and
their mains; remaining residual packet/data obligations; packet/no-cell and
exclusion-to-radius bridges; energy and seven-class premises.

Next concrete step: on a run containing `d70898ab`'s successor, read the first
N2337 kernel error; if none, proceed to the N2337 wrapper then Seven/Eight.
ROOT-IMPORT REQUEST: none.

## 2026-10-30 - part 135 (CI queue blocked upstream)

Did: checked the refreshed `LATEST.md` (timestamp 13:11 UTC) and confirmed run
`41050329106` is still the latest in its header, at `d70898ab`; it predates all
local N2337/Seven/Eight modules. The log shows the run now dies earlier with
exit 137/OOM in unrelated `SharedMomentConcreteSwitchBatch`
(`OOM-GUARD`, 863MB available), so no lane-C target receives a kernel verdict.
Re-ran the N2337 paired emitter successfully and confirmed its exact output
hashes remain `4b6553…117e` (certificate) and `b28e28…e6e0f` (main). Forbidden
token scan and `git diff --check` exit 0. Static/emitter scope only.

Unproved: unchanged; all seven singleton chains, N2337, Seven, Eight and mains
remain **CI pending**. Next: when a run reaches lane-C targets, read the first
N2337 kernel error; otherwise do not reorder targets around the upstream OOM.
ROOT-IMPORT REQUEST: none.

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

## 2026-10-30 - part 137 (N3792 archive restoration)

Did: restored the next-smallest clean unrecovered archive certificate (`N3792`,
29,399 B), extended the deterministic singleton emitter, and generated the
conditional B13 wrapper/main pair. This is a new residual refinement candidate,
not a paid theorem.

Files / SHA256 (lowercase):
- `n11-work/lean/N11Formalization/EnergyRefineN3792.lean`
  `66e978317d4c0d7caa4f26402c532de61d7746e34c9a9ac544751cab656f3d6d`.
- `n11-work/lean/N11Formalization/EnergyTerminalBatchB13Refine3792.lean`
  `fef4da0061a9574bc768a02c5486b3efb60c7d0342c53703fb42ebe81f0d5f92`.
- `n11-work/lean/N11Formalization/EnergyTerminalBatchB13Refine3792Main.lean`
  `ccd52a7f324f7807c2161d69608a993183bdc07450346a678a0217ab841707e8`.
- `n11-work/ops/lanes/C/energy-refine-n3792-tree-audit.json`
  `ae983f075a240c7e63af62344e52153ca2222df2ed1f91d2386eae17b22505cf`.
- `n11-work/ops/lanes/C/emit_refine_singleton.py`
  `2b5d86b95efa9f86d814940bdc3a7f593b74ad0d70f9509850c28f72d07f2436`.
- `n11-work/ops/lanes/C/TARGETS.txt`
  `04c1410751b70de601a3a750c0298e120a8ff5c87143e1b74dbbbfce25948ac5`.

Checks (exact scope): the exact integer tree audit passed 100/100 root-scale
entries and 200/200 split inequalities, root
`(false,2,6,475136,1,2)`, both children terminal. The 57-component Next1182
audit has union 1182, largest component 21, and 3792 in no component.
Forbidden-token scan and `git diff --check` exited 0. No local Lean kernel or
axiom result exists: all three 3792 targets are **CI pending**, so no credit.
The emitted wrapper's machine-checked `paid_count = 1998` remains conditional
on that target building.

Still unproved/missing: CI exits/axioms and MPacket validity for N3792 (and all
earlier pending chains); 320 residual certificate/data ids after nine
candidates; packet/no-cell and exclusion-to-radius bridges; energy and
seven-class premises.

Next: when CI reaches lane C, read the first N3792 kernel error; fix only that
error, then proceed through its wrapper/main. If green, fold 3792 into the
combined refinement and replace the singleton paid count with the combined
count. Do not claim payment before CI. ROOT-IMPORT REQUEST: none.
