# Lane C notes

## 2026-10-28 — earlier m-row tooling and exact next512 audit (condensed)

- `lean/N11Formalization/PaidCellCertificateM.lean` generalizes the packet to
  `m` nonnegative DBM rows and has `of7_valid`; drafted, CI pending. SHA256
  `81DB0736EF6AF2BB628103FC9AB1874F25B12E3C06494F0FE5BAA0D8A6C2E5A7`.
- `ops/lanes/C/emit_mrow_packets.py` is a fail-closed exact bridge from
  fixed-`m` JSON to packet modules; synthetic `m=4`/`m=10` preflights pass but
  no payment module exists. SHA256 `75C08E89B81E89819DDD10A16498AA2C4A0C21FE3829689DF2EDE59A88460D77`.
- `recheck_next512_rows.py` and `certify_next512_row_cap.py` rechecked all 512
  public next512 records with `Fraction` and exact `piLo/piHi`: 505 pass, 7 fail;
  a 90-row cap excludes all seven exactly, tightest margin `7.388363154221271e-7`
  at node 2356. Scope is this public artifact only, no kernel credit.
- The 389 census is reconstructed by `build_residual389_census.py`; 382 HOST
  records are absent, so the 0/7 result does not transfer to all residuals.

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

## 2026-10-28 — supplement/core byte restore + HOST asset audit (session part 2)

Did:
- Re-read `GUIDANCE.md`, `LANES.md`, this file and `ops/ci/LATEST.md`
  (`no run yet`); ran `python tools/project_status.py --check` successfully
  (scope: index/manifest declarations only).
- `make` is absent in this sandbox, so invoked the pinned restorer directly.
  Restored `assets/replay/n11-supplement` into `build/n11-wip`: 1,364 files,
  636,941,175 bytes, all SHA256s verified; package-index SHA256
  `e7fca1ae0c2f7b4548105a98c3b6c2318f3ede64bc94a2962af2a0a8b679bca4`.
- This supplement contains only C450 evidence: four non-log files, namely
  `batchv2-results-20261014-165623.json` and two C450 HOST packet files plus
  `ACCEPTANCE-CX081.json`. It contains no energy-cell generator or `f0Lo`
  records.
- Restored the 2,383-file main WIP bundle into a fresh directory
  `build/n11-core-assets`: 137,601,778 bytes, all SHA256s verified; package
  index hash `2aa324a3b127cd207bccdfc1cb7249acc96d6df7b1b80825ca373ef2030ba15d`.
  A direct merge into `build/n11-wip` was correctly refused because the two
  frozen bundles carry differing bytes at
  `evidence/c450-emit-20261014/batchv2-results-20261014-165623.json`; both
  copies were preserved.
- Audited both restored trees. The only file containing the distinctive HOST
  key `f0Lo` is `paid16-general-next512.json` (512 records, 505 passing, seven
  known failures). The energy package tar contains that same input but no
  survey generator. The 382 residual HOST records are still unavailable.

Checks run (scope stated):
- `python tools/project_status.py --check`: PASS; navigation index only.
- `restore_frozen_assets.py` twice: exit 0, frozen byte hashes verified; no
  mathematical replay or Lean build was performed.
- `rg -l 'f0Lo|HOST|energy.?cell|EnergyCell'` over both restored asset trees:
  only the known next512 input and C450 host JSONs; no generator/data for the
  382 ids.

Still unproved / missing:
- All 389 residual energy cells remain unpaid. The seven public cells stay
  excluded only under the 90-row cap; this is not the arbitrary-center proof.
- No source supplies the 382 missing HOST records. Restoration success is not
  a proof and adds no terminal credit.

Next concrete step: reconstruct the HOST record generator around the exact
formulas already exposed by `ConvexMinorantCore` (`W = RoundedPaid16.mix`,
`g`, `f0Lo`, `lamB`, `lower`) and validate it by reproducing known next512
records exactly before applying it to the 382 ids.

## 2026-10-28 — independent next512 formula recomputation (part 4)

Did:
- Added `recompute_next512_formulas.py`. It derives `W` from all 16 accepted
  field weights and `beta`, then recomputes `cl`, all nine `g` entries,
  `f0Lo`, `lamB`, and `lower` with `Fraction`; it also checks every
  reduced-cost inequality, beta probability vector, pass flag, and the frozen
  proposal hash. Stored `cl/g/f0Lo/lamB/lower` are no longer trusted.

New-file SHA256: `recompute_next512_formulas.py`
`2A4F29314FC62D6688E57E4DEAE5DC09F6E125205F03508D91F40A2F2ACEB4A8`.

Checks run (scope stated):
- `python3 -m py_compile .../recompute_next512_formulas.py`: exit 0.
- `python3 .../recompute_next512_formulas.py`: exit 0; exactly 512 records
  recomputed, 505 passing, the same seven failures `1409,2337,2341,2356,
  2360,2368,2370`. Python evidence only, not kernel credit.

Still unproved / missing:
- The 382 non-public HOST records remain absent; this does not pay any
  residual cell or extend the 90-row exclusion.

Next concrete step: use the now-validated formulas to build a deterministic
per-cell constructor/auditor that accepts a candidate `beta`, 36 minorant
lines, and dual rows, then search the 389 residual DBMs for passing candidates.
