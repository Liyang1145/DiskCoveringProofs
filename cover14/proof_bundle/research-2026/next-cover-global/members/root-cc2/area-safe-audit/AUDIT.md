# root-cc2 area-safe-audit: audit of the cover-to-angle geometric interface
# (lead/AREA-SAFE-RELAXATION.md, sections "Geometric necessary interface" and
# "Rigorous supporting-plane certificate")

Scope `members/root-cc2/area-safe-audit/` (only). Lead artifacts read-only.
**No claim registered** (lead instruction). The lead's counts (the 441 exclusions, the
bounded-catalogue pass) are **not** audited here; only the geometry-to-angle reduction is.

> **Correction log (this revision).** Four false assertions of my earlier version are
> withdrawn: (i) "tangents from an interior point `c_i` to `S^1`" — no such tangents exist;
> (ii) "the facet triangle `c_i p q` is isosceles, `beta = pi - 2*(base angle)`" — it is
> not isosceles in general; (iii) "cap monotonicity is not needed" — it is needed
> (`cap(rho) <= cap(U)` for `rho <= U`), and it holds by
> `h'(L) = (L cos L - sin L)/L^2 < 0` since `(sin L - L cos L)' = L sin L > 0`;
> (iv) "convexity checked on a grid" — convexity of `g` is immediate from
> `g'' = sin theta >= 0`. The corrected arguments are in sections 1, 2, 3 and 7.


## Verdict

The repaired interface is **sound**. The earlier `f(alpha)` relation is genuinely not used
anywhere in the derivation, the angle domains are correct, the chord/inner-norm step is
correct and in fact gives a strict inequality, the area decomposition is exact, and the
supporting-plane step is an exact identity. One wording point in the outward-clip
paragraph is imprecise but harmless (analysed in §7). Evidence:
`evidence/geom01_I1_I8.txt`, `evidence/geom03_I6legal_I7.txt`.

## 1. Angle domains (`alpha, beta in [0,pi]`)

* `beta_e`: the triangle `c_i p q` with base the Voronoi facet `pq` is **not in general
  isosceles** (`|c_i p|` need not equal `|c_i q|`), so the formula
  `beta = pi - 2*(base angle)` is invalid and is not used. What is true and needed is
  `beta_e < pi`: the facet lies on the supporting line of the (convex) cell at `pq`, and
  that line does not pass through `c_i`, so `p - c_i` and `q - c_i` have strictly
  positive projection along the inward normal of that line; hence the angle between them
  is `< pi`. Inserted fan diagonals are assigned `beta_e = 0` by construction. `beta_e >= 0`
  is trivial.
* `alpha_i < pi`: **there are no tangents from an interior point `c_i` to the unit
  circle** (my earlier phrasing was wrong and is withdrawn). The correct argument: the arc
  endpoints `p, q` are on `S^1`, and `c_i` lies strictly on the origin's side of the
  endpoint chord. Writing the outward chord normal `n`, both `p - c_i` and `q - c_i` have
  strictly positive projection along `n`; therefore the angle `alpha_i` between them is
  strictly `< pi`. `alpha_i >= 0` is trivial. (The step `norm(c_i)^2 <= 1 - rho^2` with
  `rho <= 1` puts `c_i` strictly inside `S^1`; only `alpha_i >= 0` is used in the
  certificate.)

## 2. The chord / inner-norm argument

* `norm(c_i)^2 <= 1 - rho^2 <= cos^2(theta_i/2)` needs `rho <= 1`, true after
  normalising `D` to unit radius and `rho = (r+eps)/R_eps < 1`; the exact algebra is
  `1 - rho^2 <= 1 - sin^2(theta_i/2) = cos^2(theta_i/2)`.
* Since `c_i` lies at distance at most `cos(theta_i/2)` from the origin **on the origin's
  side of the chord**, `c_i` is in the chord/arc lens, i.e. strictly interior to `S^1`.
  Combined with §1, `p - c_i` and `q - c_i` both have positive projection along the
  outward chord normal, which is what gives `alpha_i < pi`. (I previously dressed this up
  with "tangents from an interior point"; there are none — that phrasing is withdrawn and
  replaced by the projection argument above, which is the lead's.)

## 3. Area decomposition and the triangle bound

* The disk decomposes into: for each boundary site `i`, the curved wedge `W_i` (the part
  of the disk between the two rays from `c_i` to the arc endpoints — the only region where
  `c_i` can be the nearest site inside the disk, because elsewhere on the arc the
  perpendicular through `c_i` points off the arc's visible interval), and, for each facet
  `pq` (or fan diagonal), a straight-facet wedge. I verified the **total** decomposition
  reproduces the disk area:
  `Sigma_i area(W_i) + Sigma_e rho^2 sin beta_e = Sigma_i [rho_i rho_i' sin alpha_i/2 +
  (theta_i - sin theta_i)/2] + Sigma_e rho^2 sin beta_e` matches the control's
  `area = 3.1415926535897922 = pi` (scaled); the lead's own control
  `area-safe-geometry-control.json` reports `area = pi` with
  `angular_sum_max_residual = 8.9e-16` and `congruence_angle_residual = 1.6e-15`.
* `area(W_i) = (rho_i rho_i' sin alpha_i)/2 + (theta_i - sin theta_i)/2`: exact
  (triangle plus cap).
* Triangle bound: `(1/2) rho_i rho_i' sin alpha_i <= (rho^2/2) sin alpha_i` because
  `sin alpha_i >= 0` on `[0,pi]` and `rho_i rho_i' <= rho^2`. **Important: this uses only
  `sin alpha_i >= 0`, i.e. no assumption on `alpha_i` versus `pi/2`** — that is precisely
  the assumption the retracted `f(alpha)` version got wrong.
* Cap sum: `(theta_i - sin theta_i)/2 <= (theta_i/2)(1 - sin L/L)` by convexity of
  `g(theta) = theta - sin theta` on `[0,L]`; convexity is immediate from
  `g''(theta) = sin theta >= 0`, **not** from sampling (my earlier "checked on a grid"
  was a numerical support, not the proof). With `g(0) = 0` and `g(L)/L = 1 - sin L/L`,
  summing against `Sigma theta_i = 2pi` gives `cap(rho) = pi(1 - sin L/L)`, `L = 2 asin rho`.

## 4. Site-angle equations

`alpha_i + Sigma_{e incident i} beta_e = 2pi` for a boundary site: the `2pi` of angles at
`c_i` splits into the cap wedge (`alpha_i`) plus the angular extents of the incident
facets. `Sigma_{e incident i} beta_e = 2pi` for a hidden site. Both hold because the
triangulated dual disk graph spans all cells. Valid.

## 5. The total inequality

`pi <= cap(rho) + (rho^2/2) Sigma_i sin alpha_i + rho^2 Sigma_e sin beta_e`, with
`alpha, beta` satisfying the linear equations. This is an upper bound on the unit disk
area, so it is a **necessary** condition for a cover — the relaxation direction is
correct. With the control's numbers, `actual cap area = 0.2065 <= cap bound = 0.2341` and
the evaluated bound `3.188 > pi`, so the relaxation is correctly not exclusionary at the
candidate radius (consistent with the lead's report).

## 6. Supporting-plane certificate

The chain is: concavity of `sin` gives `a_j sin t_j <= a_j(sin t0_j - t0_j cos t0_j) +
a_j cos t0_j t_j`; subtract `y^T(Bt - 2pi 1)` (identically zero for legal `t`); maximise
each `(a_j cos t0_j - p_j) t_j` over `[0,pi]`. I tested the resulting inequality in an
independent implementation with a genuine incidence matrix `B` (boundary rows with one
`alpha` entry plus incident `beta` entries; hidden rows with incident `beta` entries only),
random legal `t`, random rational `t0` and `y`: **0 violations in 45 legal samples, 0 in
300**; and it fails for illegal `t`, confirming the test discriminates. The `2pi Sigma_i
y_i` term and the `pi max(0, ...)` box maximum are both correct.

**Caveat worth recording:** the certificate is an upper bound on the relaxation, hence a
valid exclusion tool, but it is not by itself a proof that the relaxation's maximum is
`< pi`; that is exactly what `area_safe_certificate.py` supplies for the 441 excluded
graphs, and it is outside this audit.

## 7. Outward clipping and the `sin L/L` monotonicity

The document writes "`sinL/L` decreases for `L in (0,pi)`" and concludes
"upper threshold valid for any `rho <= U`; ... a STRICT certificate at `U` persists for
`rho > U` sufficiently close". Two remarks:

* **The monotonicity as stated is true**, and the proof is the derivative:
  `h(L) = sin L / L`, `h'(L) = (L cos L - sin L)/L^2 < 0` because
  `(sin L - L cos L)' = L sin L > 0` and `sin L - L cos L = 0` at `L = 0`. Hence `h` is
  strictly decreasing on `(0,pi)`; equivalently `cap(rho) = pi(1 - h(2 asin rho))` is
  strictly increasing in `rho`. My first reading of the claim as false came from an
  erroneous scan interval in my own script and is retracted.
* **`cap` monotonicity is needed** (I wrongly claimed it was unnecessary): the passage
  from the certificate at `U` to configurations with `rho <= U` uses
  `cap(rho) <= cap(U)` together with `rho^2 <= U^2` — termwise domination of
  `F_rho` by `F_U`, and `cap(rho) <= cap(U)` is exactly the monotonicity above.
  My "no monotonicity at all" sentence is withdrawn. The `rho > U` side is the same
  monotonicity read on a slightly larger clipping radius.

## 8. What is not audited here

* The 441 exact exclusions and the 12-graph probe (`area-safe-certificate.json`,
  `area_safe_certificate.py`, `area_safe_probe.py`, `area_wedge_counterexample.py`) —
  counts and optimizer output; the lead reports an independent Fraction replay.
* The "finite catalogue / limit C1171 completes necessary reduction" sentence — it is an
  interface to C1171 that I did not re-derive.
* The degenerate cases (hidden full cells, zero-area facets) beyond the `beta = 0` fan
  handling, which I checked only at the level of the decomposition.

## 9. Residual gap (my reading)

None in the geometric interface itself. The load-bearing open point for the whole
programme is unchanged and is not this document's subject: turning the exclusion of the
441 graphs (at their thresholds) into a global statement needs the bounded-catalogue /
limit-C1171 interface stated in the last line of section 20 of the note, i.e. that the
finite catalogue plus the limit covers all graph systems.
