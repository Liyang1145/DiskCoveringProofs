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

## Earlier 2026-10-30 singleton chains (parts 120-122)

- N3040 wrapper/main: `EnergyTerminalBatchB13Refine3040.lean`
  `59d5f7c725bf0e9d54eb2cc7cc1bb835dbd42aeeea1f498aee8fc3b1753090e0`;
  `EnergyTerminalBatchB13Refine3040Main.lean`
  `ab6068bfe312ecdcfcd29e37e60902ab825d57956609f10416fbce06293c035b`.
- N2965 wrapper/main: `EnergyTerminalBatchB13Refine2965.lean`
  `2f1239373198d135c08d21ca9ec2016926a5badffd87f880f7d794e613e04d74`;
  `EnergyTerminalBatchB13Refine2965Main.lean`
  `785539f8304f1a72d698597b564bbd657bd0a045cf4c2135e313219ca125185c`.
- `audit_refine3040_membership.py`
  `6d43c7a7105c5face0bdd501aeff207221195862b79dd837049d2a7d47f45679`
  audits 57 Next1182 components (union 1182, largest 21) and found no 3040.
  Tree audits cover integer data only; all these chains remain **CI pending**.
- Remaining then: CI/axioms for all chains, kernel membership checks for
  B10/remaining-210, packet validity, and the energy/seven-class premises.

## 2026-10-30 - part 123 (N3440 conditional refinement chain)

Did: added a singleton-3440 B13 refinement wrapper by deterministically
emitting the audited 2965 component-bounded template, plus its conditional
main consumer. The wrapper imports `EnergyRefineN3440` and exposes
`not_paid_3440`, disjointness, paid count 1998, terminal/radius dispatch, the
refined `RemainingTerminalRadius`, and `remaining_of`. The consumer derives the
N11 main and full-disk interfaces from the refined energy premise and
`SevenClassExclusions`. Added a reproducible emitter for the remaining
singleton candidates (3589/3623/3633).

Files / SHA256 (lowercase):
- `n11-work/lean/N11Formalization/EnergyTerminalBatchB13Refine3440.lean`
  `b748c415200a7911b8f06815cb376abc3b6dedf121f99f6f5d1cd6b1ae7d3c2d`.
- `n11-work/lean/N11Formalization/EnergyTerminalBatchB13Refine3440Main.lean`
  `f54a5617e0c7726dc2912a66f52de2a541312b45c6480fed46735f890aedc6b1`.
- `n11-work/ops/lanes/C/emit_refine_singleton.py`
  `254d08b0be739b71a27ea4e75a713b701cb97bfab8f5ac72a3e9df2cecdf074a`.
- `n11-work/ops/lanes/C/TARGETS.txt`
  `e67a034c72037be0562698489ed714023e1518885b0a0d02441be85c3e7fe7e2`.

Checks (exact scope): existing N3440 tree audit is passed (100 root-scale,
200 split entries; integer tree data only). A fresh literal-inventory audit
passed: 57 Next1182 components, union cardinality 1182, largest 21
(`S07.ids55`), and neither 3440, 3589, 3623 nor 3633 occurs in any component.
`py_compile`, forbidden-token scan over both generated modules, and
`git diff --check` exited 0. No local project oleans/build were available, so
no kernel or axiom check was run. The 3440 wrapper and consumer are **CI
pending**; no theorem is claimed paid.

Still unproved/missing: CI exits/axioms for the 2341/3040/2965/3440 chains and
new targets; absence of 3440 from B10/remaining-210 still rests on kernel
`decide` (Next505 is covered by the audited bound); 328 absent certificate/data
ids after four candidate ids; residual positive-packet/no-cell bridges; seven
exclusion-to-radius bridges; refined energy and seven-class premises.

Next: check run `41037794295` first; if green, run targeted serial CI in order
`EnergyRefineN3440`, `EnergyTerminalBatchB13Refine3440`,
`EnergyTerminalBatchB13Refine3440Main`, fixing only the first kernel error.
Then inspect `EnergyRefineN3589` and emit its wrapper pair with the checked
script.
ROOT-IMPORT REQUEST: none until a refined main consumer is CI-green.

## 2026-10-30 - part 124 (N3589 conditional refinement chain)

Did: emitted the singleton-3589 B13 wrapper and conditional main consumer by
running the reproducible singleton emitter against the audited 2965 template.
The wrapper adds N3589 to the paid set, proves its absence from the old set,
derives paid count 1998 and terminal/radius dispatch, and exposes
`remaining_of`; the consumer exposes the refined N11-main/full-disk interfaces
with the refined energy and seven-class premises still explicit. Added both
modules to lane-C CI targets.

Files / SHA256 (lowercase):
- `n11-work/lean/N11Formalization/EnergyTerminalBatchB13Refine3589.lean`
  `55eb76d6ded9635f50cdb2b70eab4aba52e6d13416752155e87ea972327baea9`.
- `n11-work/lean/N11Formalization/EnergyTerminalBatchB13Refine3589Main.lean`
  `993179bd0c310f246d8a4724aa72dfe91552c3855376d7043e84f8314561d69c`.
- `n11-work/ops/lanes/C/TARGETS.txt`
  `7b1ea5e9973eea7c96cef68c0cadb584d9f08dab24fb05eeaeb70b2c994cc898`.

Checks (exact scope): `py_compile` on the emitter, forbidden-token scan over
both new Lean modules, and `git diff --check` all exited 0. The existing
N3589 tree-audit JSON reports 100/100 root-scale entries, 200/200 split
inequalities, zero mismatches/violations, root
`(terminal=false,i=1,j=6,m=491520,left=1,right=2)`, both children terminal,
and `passed=true`; it covers integer tree data only. No local project build or
kernel check was run. Both modules are **CI pending**; no theorem is paid.

Still unproved/missing: CI exits/axioms for all N2341/N3040/N2965/N3440/N3589
refinement chains; MPacket and kernel validation for N3589; 327 absent
certificate/data ids after these five candidates; residual positive-packet or
no-cell bridges; exclusion-to-radius bridges; refined energy and seven-class
premises.

Next: targeted serial CI for `EnergyRefineN3589` (if not already green), then
`EnergyTerminalBatchB13Refine3589`, `EnergyTerminalBatchB13Refine3589Main`;
fix only the first kernel error. If green, emit N3623 with the checked script.
ROOT-IMPORT REQUEST: none until a refined main consumer is CI-green.

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
