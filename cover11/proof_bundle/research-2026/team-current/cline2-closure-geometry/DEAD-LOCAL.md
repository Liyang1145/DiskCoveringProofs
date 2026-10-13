# DEAD-LOCAL — abandoned conventions and probes (cline2-closure-geometry)

Method limits and errors found while auditing the boundary closure identity.

## Wrong claims in the withdrawn draft `AUDIT-CLOSURE.md` (do not cite)
1. **"Switch = Voronoi vertex with 4 incident cells (2 rings + 2 hubs)"** — FALSE
   generically. The switch is the crossing of the ring-pair Voronoi *edge* with
   `bd D`; hubs have `|h| < 1-r` so `|P-h| >= 1-|h| > r` and are never nearest at
   the switch. Evidence: `vertex_group.py`, `exact_vertices.py`.
2. **"Fan triangulation tiles the switch polygon"** — not needed; and the earlier
   claim that sites lie *outside* `K` came from my mis-oriented dot-product test.
   Correct statement: sites are strictly *inside* `K` (Cauchy-Schwarz half-plane
   sandwich, verified in the repaired note). Evidence: `AUDIT-CLOSURE-REPAIRED.md` §2.
3. **"The supporting line of every boundary chord is at distance >= sqrt(1-r^2)
   from the origin"** — false for the tangent line; the correct and sufficient
   statement is the half-plane sandwich.

## Wrong angle conventions found and killed (both cost significant time)
* **Convention error 1 (draft 1):** taking the "angle at the switch between the
  two ring sites" as the unsigned `arccos` value. When the sector turns the other
  way this returns the *supplement*; all residuals computed this way (up to
  0.1 rad) were artifacts. Evidence: `convention_probe.py`, `diag_saved.py`.
* **Convention error 2 (my first repair message):** treating `L_i` as living at
  the current switch and pairing `T_i + 2b_i + L_i` at one vertex while the
  certificate pairs `T_i + L_(i+1)`. The correct convention (confirmed by the
  lead and re-verified here) is: `L_(i+1)` is the base angle of the **next**
  sector triangle `(P_i, c_{i+1}, P_{i+1})` **measured at the current switch
  P_i**; `T_i` is the base angle of sector triangle `i` at `P_i`; `2b_i` is the
  angle at `P_i` between `c_i` and `c_{i+1}`.
  Correct equation: `T_i + L_(i+1) + 2b_i + (w_i + w_(i+1))/2 = pi`
  (verified 9/9 to 8.9e-16 on the saved candidate and on a regular nonagon;
  `resolve_conv.py`, `decide.py`, `lead_convention.py`).
* **Wrong "cell angle at a Voronoi vertex = gap between consecutive nearest-site
  rays"** — only valid for equidistant nearest groups; my `definitive.py` /
  `vertex_cells.py` totals (not summing to 2 pi) are artifacts of this and are
  NOT evidence.
* `arcs_saved.py` (HalfspaceIntersection) fails on degenerate interior points and
  returned 2 arcs instead of 9 — discarded.

## Method limits (not mathematical negatives)
* Random genuine-cover generation for closure stress tests is delicate: the
  covering condition for 9 rings + 2 hubs at `r <= 0.38` is tightly constrained
  (ring norms ~0.84-0.90, near-equal angular spacing), and naive random hub
  placement gives covering radii 0.42-0.65 (`cover_search*.py`,
  `stress_closure.py`: 0 genuine covers found in ~4 min of Nelder-Mead search).
  The identity was therefore verified on the saved certified candidate, on a
  regular nonagon, and on a symmetric 9-ring family (residuals <= 8.9e-16), plus
  the analytic proof — not on a random sample of covers.
* The identity holds for any configuration with the cyclic 9-arc Voronoi
  structure (it is a local cone statement); "is_cover" is not needed for the
  identity itself and was used only as a sanity filter.

## Scope guards
* `(CL)` is a necessary local equation. It does not by itself give any lower
  bound; the bound comes from the certificate dual.
* The lead's sector-norm constraint is equivalent to `|c|^2 <= 1-R^2`; do not use
  it without the feasibility cut (`lead_inequality.py`, `AUDIT-CLOSURE-REPAIRED.md` §6).
