# flash-geometry DEAD / method limits

## Mathematical negatives
- **O1 (three ring disks sharing a common point) is NOT refutable on the pure
  co-point domain.** Lead reports a certified counterexample (3-ring cluster with
  margin -0.0757). My own budget test (`tools/o1_test.py`) shows the arc-union bound
  2pi-12 asin r = 1.605630 is not the obstruction either. Consequence: any O1
  exclusion must use the ring arc ledger / consecutivity, not only the co-point
  constraint. Do not register O1 as an obstruction.

## Discarded instruments (implementation/inference errors, not mathematics)
- Wrong arc half-width formula `arcsin(r/rho)` in `tools/check_cert_boundary.py`.
  Correct: `arccos((1+rho^2-r^2)/(2 rho))`, max `asin r` at `rho = sqrt(1-r^2)`.
  Only the "sum of arc widths" line of that script is invalid; its direct-distance
  boundary argmax is fine and agrees with the certified value.
- `tools/explore3.py`: near-root/far-root mix-up and "outside" orientation error in
  the ray-entry helper. Exploration only; never cited as evidence.
- `tools/reform_calib.py`: "hole extreme points" filter `min_j |p-a_j| >= r` is
  vacuous for pairwise circle intersections (distance is exactly r to two rings);
  equality points require the C458 accessibility test first. T1/T2 output invalid.
- Exhaustive O(n^3) MEB (`tools/hole_of_object.py`, `tools/hole_meb.py`) on 10^6
  sample points: time/OOM limit, killed. Grid scans are not evidence; the calibrated
  quantity must be computed from the finite critical set (pairwise ring-circle
  intersections inside the strict hole) instead.
- `tools/hole_shadow.py` hub-shadow bound `arcsin(r/(1-2r))` is undefined/inactive at
  r = .38 (1-2r = .24 < r): the two-hub angular-shadow inequality is vacuous there.
  Recorded as a method limit, not a mathematical claim. Its two .npy dumps were
  deleted (16 MB of grid data from an instrument that is not evidence).
- `tools/study1.py`: the unconstrained Nelder-Mead polish of `-min_i |x-c_i|` can walk
  outside D and returned `inf` for several ring families (0.62/0.70 rings): the
  refinement step must be constrained to D or replaced by the certified critical-set
  evaluation. Output of that script (including the 0.76+ rows) is not evidence.

## Scope guards
- A1/A2 are elementary and do not depend on the C450/C451 reduction; they do.
- The hub-free representation (A3) eliminates hub POSITIONS but not the two-centre
  condition; it does not by itself give any lower bound.
- The core-hub domain audit (A4) is an audit of necessary conditions only; no
  sufficiency for the full hole is claimed anywhere in this directory.
