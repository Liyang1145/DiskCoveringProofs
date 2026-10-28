# Lane C notes

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
