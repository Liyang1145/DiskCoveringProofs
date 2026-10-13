# CANDIDATE member status — n13/14/15 profiling, corrected

Write scope: `research-2026/next-cover-global/members/candidate/` (only).
Old n11/n12/type14 assets read-only. No precision/optimality claims.

## Current claim level

- **numeric portrait only** (see `CORRECTION-and-status.md` and `evidence/profile_corrected.json`).
- A previous report (`REPORT-n13-14-15.md`) contained interface errors; the correction file
  supersedes its structural statements. Do not build on that file.

## What is established (numeric, reproducible)

- n=14's saved high-precision object `session2/type14/out/hprec_sol.json` has **exact D2 symmetry**
  (σx, σy and C2 all map the centre set to itself with residual 0.0 at source precision).
  Full D2 orbits: **2 orbits of 4** (`[0,1,2,3]`, `[4,5,6,7]`) + **3 orbits of 2**
  (`[8,9]`, `[10,11]`, `[12,13]`).
- Voronoi vertices inside D, nearest-site filtered: **n13 = 14, n14 = 16, n15 = 17**
  (raw triple circumcentres inside D are 237/296/377 — a different object).
- n=14: 14 of the 16 Voronoi vertices satisfy f == R to source precision; 2 are lower by
  1.09e-2. Boundary-active = {0..9}; non-boundary = {10,11,12,13}.
- Core mechanism check for n=14 (a = 1-2U = 0.3365359314): no boundary-active disk touches
  |x| = a; the four non-boundary disks cover it with max-min 0.267289 <= U.

## Known-bad / withdrawn

- D2 orbit count stated as "7 orbits of 2" (that is C2's orbit structure).
- "237/296/377 Voronoi vertices" (they are raw triple circumcentres).
- A list of "tight triples" for n=14 ({0,2,3} etc.) — hand recomputation gives circumradii
  0.3268/0.2781/0.2640/0.2384/0.3172/0.2081, none equal to R, and none is a nearest-site
  (Voronoi) vertex for its triple.
- Symmetry claim for n13/n15 based on x/y-axis tests only; full-axis search gives best mirror
  residuals 1.13e-2 (n13, axis 138.46 deg) and 3.80e-3 (n15, axis 39.0 deg), and n15's
  C2 nearest-neighbour map is not an involution.
- "f - R ~ -5e-17 means exactly tight": withdrawn phrasing; float residuals are not exactness.
- `n14_exactification.py` and the extrapolation in `n14_core.py`'s first version: not usable
  until the interface fixes are re-run.

## Next executable step (blocked until the interface fix is verified)

Regenerate the nearest-site-filtered active candidate set for n13 and n15 as well, then
re-run an independent second-path computation of at least one Voronoi vertex per n
(e.g. by solving the three nearest-site equality conditions directly with exact rational
arithmetic on the 17-digit literals) to confirm index/coordinate interfaces before any
exactification or exact-root work.
