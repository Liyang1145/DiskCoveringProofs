# Lane C notes

SUPERVISOR (2026-10-29 00:45 CST): Pivot. Only 7 of the 389 residual cells have public HOST records; the other 382 are missing. Do NOT wait for them. (1) Restore the generation supplement: `cd /workspace/projects/ae3385e7-f93b-4bd2-a917-5a9561f457b7/repos/DiskCoveringProofs && make restore-n11-supplement` (downloads hash-bound generator/oracle assets into build/n11-wip), find the HOST/energy-cell generator and the per-cell data (field values, dual rows) for terminal ids in residual389-census.json. (2) Regenerate records for the 382 ids yourself (exact Fraction), then attempt the m-row dual with exact Farkas rounding. (3) Local `import Mathlib` in mathlib-probe takes >120 s on this host: give probes `timeout 600` or rely on CI.


## 2026-10-28 — generic row cap + exact next512 audit

Did:
- Read `GUIDANCE.md`, `LANES.md`, latest CI (no run), ran
  `python tools/project_status.py --check` (index check passed).
- Added `lean/N11Formalization/PaidCellCertificateM.lean`, a row-count-generic
  `Packet (m : ℕ)` / `Valid` / `oracle_gt` / `common_chart_radius` API. It is a
  direct generalization of `Paid16CellCertificate`; `m` occurs only in the
  nonnegative DBM-row data, while the genuinely valid field mixture stays the
  existing `Fin 16`/36-line packet. No root import requested yet.
- Added `ops/lanes/C/recheck_next512_rows.py` and its generated
  `ops/lanes/C/next512-row-extension-results.json`. The script parses the frozen
  integer DBM matrices, uses exact `Fraction` arithmetic and the exact rational
  `piLo/piHi` from `Interval/Trig.lean`, and uses a float scipy/HiGHS LP only to
  search candidate row multipliers.

New-file SHA256: `PaidCellCertificateM.lean`
`54EC68D4EF19FDC7C9F77361B7C42FB6D808F1A08A721217A2798BC6BF4AAD12`;
`recheck_next512_rows.py`
`7A76A7AF6B7A9051B8EAC1AC9277C5A3818C662760AB66C3982F0A7A274D4CA5`;
results JSON
`DDCF31107B7E80A172E1053C16788390AE82A4537C1BCBBEE9EECDBE2B8D3D35`.

Checks run:
- `python tools/project_status.py --check`: PASS; scope = index/manifest only.
- `PYTHONPATH=/tmp/lanec-scipy python3 recheck_next512_rows.py`: exit 0.
  Input hashes: proposal `F49F06FC57A818E464D8DCBDAACE2E4D57A3C2E84CEA27FE86C4551363F3DD16`,
  DBM `BD4E71CB29804A5A3D5953727558F4656D23253A83B69F5C3D6E25EEB4EA8ED5`.
  All 512 frozen `lower = f0Lo - lamB + rmin` and `pass ↔ lower > T^2`
  identities rechecked exactly; 505 pass / 7 fail as recorded.
- All-90-ordered-pair LP search on the seven public failures: **0/7** obtain a
  strict exact-rational pass after `limit_denominator(10^18)`. Best exact gaps
  remain negative: 1409 `-1.3866391797e-5`, 2337 `-1.0365427704e-5`, 2341
  `-1.9843152153e-5`, 2356 `-7.388363308e-7`, 2360 `-1.7193773531e-5`, 2368
  `-4.9659404040e-5`, 2370 `-3.7366048307e-5`. Scope is the public next512
  artifact only, not the full 389-cell census.
- `PaidCellCertificateM.lean`: drafted, CI pending. No local full-project build
  was attempted (sandbox has no project oleans).

Still unproved / missing:
- The 389 census itself is not present here; do not transfer the 0/7 result to
  all 389. The seven public failures also need an exact infeasibility/Farkas
  certificate if the negative row-cap conclusion is to be kernel- or
  rational-certified rather than float-LP evidence.
- CI has not kernel-checked `PaidCellCertificateM`; it is not paid.

Next concrete step: convert one HiGHS dual solution for a failing cell into an
exact rational Farkas certificate for the 90-row LP (or locate the missing 389
records and run the same exact search there); then decide whether the residual
needs new harmonic fields rather than more rows.

## 2026-10-28 — exact 90-row cap exclusion for all seven public failures

Did:
- Added `certify_next512_row_cap.py` and generated
  `next512-row-cap-certificates.json`. HiGHS only suggested seven small dyadic
  dual weight vectors; every certificate hypothesis and conclusion is checked
  with `Fraction` from the frozen JSON/DBM and exact `piLo/piHi` bounds.
- Each certificate gives `y >= 0`, `sum y = 1`, and
  `sum_q y_q row_a(i,j,q) <= db(i,j)/4096` for all 90 ordered pairs. It therefore
  bounds every attainable 90-row gain by `sum_q y_q endpointLo(g_q)`. All seven
  bounds are strictly below `T^2 - f0Lo`, excluding a pass for each public
  failure, including near-misses 2356 and 2360.

New-file SHA256: `certify_next512_row_cap.py`
`0139CCEBB37ED23B09CDBDFB75294FD41B8A2149435F4B8CAA70EB005C5DB83B`;
`next512-row-cap-certificates.json`
`A5939E05C90824B61488D0CD3B65A9A5361CE5C59D71B1ADD9F082E8A116BCEB`.

Checks run:
- `python3 -m py_compile certify_next512_row_cap.py`: exit 0.
- `PYTHONPATH=/tmp/lanec-scipy python3 certify_next512_row_cap.py`: exit 0.
  512 frozen records checked; all seven public failures excluded exactly;
  input hashes proposal `F49F06FC…DD16`, DBM `BD4E71CB…8ED5`.
- Tightest exact margin is node 2356: `7.388363154221271e-07 > 0`.

Still unproved / missing:
- No kernel module consumes these certificates; the scope is the public
  next512 artifact under the 90-row cap, not the full 389-cell census.
- The 389 census and the 35 zero-dual records remain missing here. This result
  does not prove that additional rows or harmonic fields are unnecessary for
  those cells.
- `PaidCellCertificateM.lean` remains drafted, CI pending (hash unchanged:
  `54EC68D4EF19FDC7C9F77361B7C42FB6D808F1A08A721217A2798BC6BF4AAD12`).

Next concrete step: locate the 389 census; run `certify_next512_row_cap.py`'s
exact cap-bounding procedure on its 354 method failures + 35 zero-dual ids, and
emit a separate exact certificate file for every cell it excludes.

## 2026-10-28 — exact 389-id census reconstructed (part 2)

Did:
- Added `build_residual389_census.py`, which reconstructs
  `terminals - sharpIDs - paidIDs` from the frozen Lean ID data rather than
  relying on a missing stored census. It parses 2506 `terminal := true` nodes,
  the 120 `Patch120DomainPacket.patchID` entries, 1961 generated packet IDs
  (`Paid16General*.nodeID`/`idsNN` plus `Paid16Batch22Packet.nodeID`), and the
  36 older `paid_ids` recorded in the frozen next512 input.
- Its assertions verify 1961 + 36 = 1997 paid IDs, disjointness with all 120
  sharp IDs, and exactly 389 residual terminal IDs. Generated
  `residual389-census.json` with the complete sorted ID list.
- Residual-list SHA256 (comma-separated decimal IDs):
  `747447E233634FBC9D9321824148165AC866105FE0367AED27F6F8D9A2E07F46`.
- The 389 intersect the public next512 survey in exactly the seven already
  excluded failures `1409,2337,2341,2356,2360,2368,2370`. The other 382 HOST
  records are absent locally.
- Checked older local diagnostics: 40 residual ids occur in
  `lead/dbm_norm_secant.json`, but its component-secant upper has
  `certified_C919 = false` for all 40 (norm upper range 0.009102..0.020383);
  nine residual ids occur in `lead/remaining_dbm_diagnostic.json` with numeric
  `pair_gap` about 4.8e-6. Neither is a kernel or exact HOST-energy payment.

New-file SHA256:
`build_residual389_census.py`
`3A19D3B62DC571673498178F61711A40AF3449E7B5E84588013B3060328537B6`;
`residual389-census.json`
`2242186B79341977E39A97CAB9C9040015145E846421E4766970D36FF18FF8F4`.

Checks run (scope stated):
- `python tools/project_status.py --check`: PASS; index/manifest declarations
  only, not mathematics or full byte integrity.
- `python3 -m py_compile build_residual389_census.py`: exit 0.
- `python3 build_residual389_census.py`: exit 0 on rerun; asserted 2506
  terminals, 120 sharp, 1961 generated paid, 36 base paid, 1997 total paid,
  and 389 residual. Input hashes are embedded in the JSON; DBM remains
  `BD4E71CB…8ED5` and next512 input remains `F49F06FC…DD16`.
- Cleaner of the census ID list is exact set arithmetic over frozen source;
  no LP/kernel conclusion is drawn from it.

Still unproved / missing:
- All 389 cells remain unpaid. Seven are excluded only under the 90-row cap by
  exact-rational certificates; that is not a general energy proof.
- HOST survey records (`f0Lo`, `g`, packet rows, etc.) for 382 residual ids are
  not in this worktree, so the row-extension/row-cap procedure cannot yet run on
  them. The 40 secant and 9 remaining-DBM diagnostics are numeric/partial and
  do not certify the required energy inequality.
- `PaidCellCertificateM.lean` is still CI pending; no CI run exists.

Next concrete step: obtain the missing 2386-cell HOST survey (or at least its
382 residual records), then run `recheck_next512_rows.py` and the exact
row-cap search on those records; group exclusions by shared dual weights so
they can be emitted as small Lean certificate modules.

## 2026-10-28 — residual asset audit + generic-packet compatibility (part 3)

Did:
- Re-read `GUIDANCE.md`, `LANES.md`, this notes file, and CI (`no run yet`).
  Ran `python tools/project_status.py --check` (index check passed).
- Searched every local JSON (including ignored/restored trees) for the HOST
  survey's distinctive `f0Lo` key: the only file is
  `n11-work/evidence-20261028/inputs/paid16-general-next512.json`. Thus the
  other 382 residual records are genuinely unavailable in this worktree, not
  merely undiscovered under another filename.
- Extended `lean/N11Formalization/PaidCellCertificateM.lean` with `of7` and
  `of7_valid`: every frozen `Paid16CellCertificate.Packet` with a `Valid`
  proof embeds as the `m = 7` instance of the row-count-generic API. This
  gives CI a concrete consumer of all generic fields without claiming new
  energy.

New module SHA256: `PaidCellCertificateM.lean`
`81DB0736EF6AF2BB628103FC9AB1874F25B12E3C06494F0FE5BAA0D8A6C2E5A7`.

Checks run (scope stated):
- `python tools/project_status.py --check`: PASS; index/manifest declarations
  only, not mathematics or byte integrity.
- Forbidden-token grep on the module: no `sorry`, `admit`, `native_decide`,
  `Lean.ofReduceBool`, `implemented_by`, or `maxHeartbeats 0`.
- Exhaustive local `f0Lo` JSON search: one source file only; exact next512
  input hash remains `F49F06FC…DD16`.
- `PaidCellCertificateM` plus `of7_valid`: drafted, CI pending. No local Lean
  build was attempted because this worktree has no project oleans.

Still unproved / missing:
- All 389 residual cells remain unpaid. Seven are excluded only under the
  90-row cap; `of7_valid` is API compatibility, not a new energy certificate.
- The 382 other HOST records, including their `f0Lo`, `g`, and packet rows,
  are absent. No row-extension or Farkas search can be run on them here.
- CI has not yet kernel-checked the generic module or the new compatibility
  lemma (`ops/lanes/C/TARGETS.txt` already lists it).

Next concrete step: when CI runs, inspect errors in `of7_valid` first; then
obtain/export the 382 missing HOST records by exact hash and run the existing
exact row-cap procedure before attempting per-cell packet emission.

## 2026-10-28 — part 4: probe of `of7_valid` proof shape

Did:
- Re-read GUIDANCE/LANES/notes/CI (`no run yet`).
- Audited `PaidCellCertificateM.of7_valid` against the frozen
  `Paid16CellCertificate.Packet/Valid` definitions (field types and proof
  arguments line up; `mix`, `mix_nonneg`, `mix_le` signatures confirmed).
- Built a Mathlib-only structural probe at `/tmp/probeC.lean` modelling the
  dependent `Packet m`/`Valid` projections and the exact
  `simpa only [of7, W]` pattern used in `of7_valid`.

Checks run (scope stated):
- `python tools/project_status.py --check`: PASS (index/manifest only).
- Probe command `lake env lean /tmp/probeC.lean` under
  `/workspace/tools/mathlib-probe`: started; result not yet observed in this
  4-minute slot (no project-module kernel check was attempted).

Still unproved / missing:
- `PaidCellCertificateM` remains drafted, CI pending; the probe is not a
  substitute for kernel-checking the imports/dependent fields of the real
  module.
- All 389 residual cells remain unpaid; 382 HOST records still absent.

Next concrete step: read the probe outcome; if it fails, fix the `of7_valid`
`simpa` set (likely add `packet` projection lemmas); otherwise wait for CI and
inspect its first error, then pursue the missing 382 HOST records.
