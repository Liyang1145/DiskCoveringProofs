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

## 2026-10-30 - part 125 (N3623 conditional refinement chain)

Did: emitted the singleton-3623 B13 wrapper and conditional main consumer with
`emit_refine_singleton.py 3623` from the audited 2965 component-bounded
template. The wrapper adds N3623 to the paid set, proves disjointness and paid
count 1998, and `remaining_of`; the consumer exposes the refined N11-main and
full-disk interfaces. Appended both targets.

Files / SHA256 (lowercase):
- `n11-work/lean/N11Formalization/EnergyTerminalBatchB13Refine3623.lean`
  `5ffc59741a3de3ce546e9311829c7e7c35fa2fa6244b62dfb192d93eab291679`.
- `n11-work/lean/N11Formalization/EnergyTerminalBatchB13Refine3623Main.lean`
  `9a6b54bade99a4b94019b2d5b04bdcf0a302c0ec277903d48425dc8a8bd2e611`.
- `n11-work/ops/lanes/C/TARGETS.txt`
  `8c680851bd89c5659ef4c11acfb0abdb5fc151b608b76db6297a7ffd6f6fedae`.

Checks (exact scope): existing N3623 tree audit JSON passed 100/100 root-scale
entries and 200/200 split inequalities, root
`(terminal=false,i=1,j=6,m=507904,left=1,right=2)`, both children terminal;
integer tree data only. Fresh inventory audit: 57 Next1182 components, union
cardinality 1182, largest 21 (`S07.ids55`), 3623 in none. `py_compile`,
forbidden-token scan, and `git diff --check` exited 0. No project build or
kernel check was run; both new modules are **CI pending**, and no theorem is paid.

Still unproved/missing: CI exits/axioms for the N2341/N3040/N2965/N3440/N3589/
N3623 chains; packet/kernel validation for 3623; 326 certificate/data ids after
six candidates; B10/remaining-210 absence rests on kernel `decide`; residual
positive-packet/no-cell bridges; exclusion-to-radius bridges; refined energy and
seven-class premises.

Next: query run `41037794295` and newest CI, then run targeted serial CI for
`EnergyRefineN3623`, its wrapper, and main consumer; fix only the first kernel
error. If green, emit N3633 with the checked script.
ROOT-IMPORT REQUEST: none until a refined main consumer is CI-green.

## 2026-10-30 - part 126 (N3633 conditional refinement chain)

Did: emitted the final recovered-residual singleton pair, N3633, with
`emit_refine_singleton.py 3633` from the audited 2965 template. The wrapper
adds 3633 to the B13 paid set, proves old-set disjointness and paid count 1998,
dispatches terminal/radius obligations, and exposes `remaining_of`; the main
consumer exposes the refined N11-main and full-disk interfaces. Generalized
`audit_refine3040_membership.py` to accept a target id (default 3040) and
appended both modules to lane-C targets.

Files / SHA256 (lowercase):
- `n11-work/lean/N11Formalization/EnergyTerminalBatchB13Refine3633.lean`
  `5f6e51a4f95f08239a8669b51f917fc0ff32ca20539581e233e48823b0301dbf`.
- `n11-work/lean/N11Formalization/EnergyTerminalBatchB13Refine3633Main.lean`
  `094265d3996ae5ae0b37c95e784fbe7d648c22f30aab8433c2970e45d8a7abdb`.
- `n11-work/ops/lanes/C/TARGETS.txt`
  `b71d7f00f7bf18b104d83b9eec2d729ccbda54869f14d33e5f577937420b0cfe`.
- `n11-work/ops/lanes/C/audit_refine3040_membership.py`
  `31d9e5b5f05489e8568e1a63e636a73751bd6ce405c067bdda9430fd3bb0ed4d`.

Checks (exact scope): run `41037794295` is green for `EnergyRefineN3633`
(`dfe0881a`). The stored N3633 tree audit reports 100/100 root-scale entries,
200/200 split inequalities, zero mismatches/violations, root
`(terminal=false,i=1,j=6,m=507904,left=1,right=2)`, both children terminal;
integer tree data only. Fresh literal inventory audit: 57 Next1182 components,
union cardinality 1182, largest 21 (`S07.ids55`), 3633 in none. `py_compile` on
both Python scripts, forbidden-token scan over the new Lean files, and
`git diff --check` exited 0. No local project build or kernel check was run;
both new modules are **CI pending**, and no theorem is paid.

Still unproved/missing: CI exits/axioms for N3633 wrapper/main and for the six
earlier refinement wrapper/main pairs; 326 certificate/data ids after these
seven recovered candidates; MPacket/kernel validity for each newly added id (the
EnergyRefine modules already carry their local `pk_ok` checks, but CI is the
authority); residual positive-packet/no-cell bridges; exclusion-to-radius
bridges; refined energy and seven-class premises.

Next: check newest CI, then build serially
`EnergyTerminalBatchB13Refine3633`,
`EnergyTerminalBatchB13Refine3633Main`; fix only the first kernel error. If the
seven singleton wrappers are green, the next engineering step is a combined
refinement consumer exposing one paid set of 2004 ids and a single weakened
energy premise, rather than seven parallel premises.
ROOT-IMPORT REQUEST: none until the combined refined main consumer is CI-green.

## 2026-10-30 - part 127 (combined seven-certificate refinement)

Did: added one combined B13 refinement consumer over the seven recovered ids
2341/3040/2965/3440/3589/3623/3633. It imports the seven singleton wrappers,
defines `newIDs` as their union and `paidIDs = B13.paidIDs ∪ newIDs`, proves
old/new disjointness by delegating to each wrapper's `not_paid_*`, counts
`newIDs.card = 7` and `paidIDs.card = 2004`, dispatches terminal/radius proof,
and exposes `RemainingTerminalRadius` plus `remaining_of` back to B13. The Main
module derives both conditional N11 interfaces (energy premise now over the
combined 2004-id paid set; `SevenClassExclusions` remains explicit). Added both
modules to lane-C targets.

Files / SHA256 (lowercase):
- `n11-work/lean/N11Formalization/EnergyTerminalBatchB13RefineSeven.lean`
  `57e5b9caa136f6562f970e4c26703dcb64c4ce72e118e111529259ff69fb6024`.
- `n11-work/lean/N11Formalization/EnergyTerminalBatchB13RefineSevenMain.lean`
  `131e4be62c98f0d95b942252b7fb711c029953d2d98c22efafbe678cf6ff0021`.
- `n11-work/ops/lanes/C/TARGETS.txt`
  `03a6687b07f64fe55aa2c4cd3ba1a4d22977e73bdbceb5d01fd4a90a5fbd7e32`.

Checks (exact scope): forbidden-token scan over both new Lean modules and
`git diff --check` exited 0. A bounded local elaboration attempt failed before
reading the new module because Lake tried to check out a stale Mathlib cache
over untracked files; a standalone Mathlib probe timed out at 120 s. Thus no
local kernel/axiom result exists for these modules. They are **CI pending**;
no theorem is paid.

Still unproved/missing: CI exits/axioms for seven singleton wrappers/mains and
the combined pair; MPacket validity for the seven ids; 322 of the 389 residual
certificate/data ids still lack candidates; residual positive-packet/no-cell
bridges; exclusion-to-radius bridges; and both energy and seven-class premises
remain conditional.

Next: read newest CI; if all seven wrapper targets are green, build serially
`EnergyTerminalBatchB13RefineSeven`, then `...RefineSevenMain`, fixing only the
first kernel error (most likely proof-pattern or import failure). If the seven
wrappers are still pending/red, fix those first rather than the combined pair.
ROOT-IMPORT REQUEST: none until the combined main consumer is CI-green.

## 2026-10-30 - part 128 (N2341 census fix)

CI artifact `41050329106` showed the seven singleton packets and the
3040/2965/3440/3589/3623 wrapper/main pairs green, but N2341 and its Main red
from the optional `residualIDs` census section (unsolved goal line 72, then no
goals line 86). Removed that section and its dangling `#check`; the paid-set,
disjointness, radius and `remaining_of` proofs are unchanged. Local
forbidden-token scan, `git diff --check`, and a structural audit exited 0.
No local kernel result; N2341/N3633/Seven remain CI pending.

## 2026-10-30 - part 129 (post-fix CI scope audit)

Did: audited artifacts for runs `41050208198` (`18c6e03b`) and
`41050329106` (`d70898ab`). Run `18c6e03b` built all seven
`EnergyRefineN*` packets with exit 0, but its lane-C `TARGETS.txt` ended at
`FrozenCapPublicExcludedTree`: it did not include any Refine wrapper/main or
the combined pair. Run `d70898ab` included only the 3040/2965/3440/3589/3623
Refine targets; the N2341 failure there is the already-removed census-only
section (`72:67` unsolved, `86:2` no goals). The current N2341 source ends the
theorem at lines 85/87 and contains no `residualIDs` block.

Checks (exact scope): unzip plus JSON exit audit for both artifacts; source
scan confirms all seven singleton packet exits are 0; forbidden-token scan over
the five current changed/new Lean files returned none; `git diff --check`
exited 0. Current SHA256 (lowercase):
- N2341 wrapper `fa379f7e2409c56dd7cee2f26900f68d50b44f5d2c7e44644154e2c6c23e4d97`
- N3633 wrapper `5f6e51a4f95f08239a8669b51f917fc0ff32ca20539581e233e48823b0301dbf`
- N3633 Main `094265d3996ae5ae0b37c95e784fbe7d648c22f30aab8433c2970e45d8a7abdb`
- Seven combined `57e5b9caa136f6562f970e4c26703dcb64c4ce72e118e111529259ff69fb6024`
- Seven Main `131e4be62c98f0d95b942252b7fb711c029953d2d98c22efafbe678cf6ff0021`
- lane targets `03a6687b07f64fe55aa2c4cd3ba1a4d22977e73bdbceb5d01fd4a90a5fbd7e32`

No kernel check has run on the current N2341 fix, N3633 pair, or combined pair;
they are **CI pending**, so no refinement credit is claimed. Still missing:
those five target exits/axiom reports; 322 residual certificate/data ids;
packet/no-cell and exclusion-to-radius bridges; energy and seven-class premises.

Next: on a run whose lane-C targets include the five pending modules, fix only
the first error, starting with `EnergyTerminalBatchB13Refine2341`; do not restore
its census section. Then require the combined Main to be CI-green before asking
for root import.
ROOT-IMPORT REQUEST: none until `RefineSevenMain` is CI-green.

## 2026-10-30 - parts 130-131 (CI queue audit)

Did: inspected `LATEST.md`; newest artifacts remain runs `41050329106` and
`41050208198`, both predating the N2341 census fix. No artifact covers current
N2341, N3633, or Seven. Re-ran source forbidden-token scan (none) and
`git diff --check` (exit 0). Moved the six unpriced refinement targets to the
front of `TARGETS.txt` so CI checks them before old green targets; removed their
duplicate entries. Targets SHA256:
`0a890e69d80ebec96bbff8a849577d71ed130e7bb7c00a74ca14234d0a24c25a`.

Scope: static source/CI-log audit only; no local kernel/axiom result. These six
remain **CI pending**, so no theorem or refinement credit is claimed. Missing:
their exits/axiom reports; MPacket validity for seven ids; 322 residual
certificate/data ids; packet/no-cell and exclusion-to-radius bridges; energy
and seven-class premises.

Next: on the next run, fix only the first error beginning with Refine2341, then
require N3633, Seven, and SevenMain green. ROOT-IMPORT REQUEST: none until green.
