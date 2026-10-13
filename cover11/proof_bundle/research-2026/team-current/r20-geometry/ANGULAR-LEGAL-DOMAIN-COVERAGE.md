# Fixed-switch angular legal domain: analytic bounds and interval diagnostics (lead 77b77bd1)

Author: r20-geometry (sole writer; no subagents; **no claim registered**).
Evidence: `angular_domain_coverage.py/.out.txt` (60-dps evaluation, outward widened by `1e-40`).
Scope: **domain coverage only** — no numerical grid, no optimisation, no SOCP solve.

## 1. Model and the two confirmation lemmas (analytic)

Nine cyclic unit points `U_0..U_8`, owned arcs of widths `Δ_i ≥ 0`, `Σ Δ_i = 2π`; `U_0 = (1,0)` fixed;
each ring disk of radius `r` covers its owned arc; the covering is by nine ring disks (plus the two
hubs, which do not own boundary arcs in this switch model). Let `c_i` be ring `i`'s centre.

**(L1) Owned-width bound (corrected, lead f657c6a6: the chord bound alone is NOT a valid route —
the complementary major arc satisfies it too).** Argument:
1. *The ring disk meets the unit circle in a single arc.* For `r < 1` and `|c_i| ∈ [1−r, 1+r]`, write
   `U = (cos θ, sin θ)` in the frame centred at `c_i`'s direction: `|U − c_i|² = 1 + |c_i|² − 2|c_i| cos θ ≤ r²`
   ⟺ `cos θ ≥ (1 + |c_i|² − r²)/(2|c_i|) =: f(|c_i|)`. Since `f(c) = (1 + c² − r²)/(2c)` has its minimum
   `√(1−r²)` at `c = √(1−r²)`, the inside-set is `|θ| ≤ α` with `cos α = f(|c_i|) ≥ √(1−r²)`, i.e. it is a
   **single** arc of width `2α` (no major-arc alternative: the condition is one interval in `θ`).
2. *Its width is at most `2 asin r`.* `cos α ≥ √(1 − r²) = cos(asin r)` ⟹ `α ≤ asin(r)` (both in `[0, π/2]`),
   so `2α ≤ 2 asin(r) ≤ 2 asin(0.38) = 0.7795930 < π`.
3. *Ownership means inclusion.* The arc owned by ring `i` lies inside that disk arc (its points are covered
   by disk `i`), hence `Δ_i ≤ 2α ≤ 2 asin(r) < π`.

So the arcs are **short because they sit inside a single disk arc of width `≤ 2 asin(r) < π`** — the
hypothesis needed by the cap argument of `TWO-CENTER-LINE-ENUMERATION-SCOPE.md` §3/§5.6 is derived, and
the chord bound is only a corollary, never the route.

**(L2) Uniform positive lower width.** From `Σ Δ_j = 2π` and `Δ_j ≤ 2 asin(r)` for the eight other arcs,

> `Δ_i = 2π − Σ_{j≠i} Δ_j ≥ 2π − 16 asin(r) ≥ 2π − 16 asin(0.38) = w_min = 0.0464445635914… > 0`.

**Analytic positivity (no numeric certificate needed; lead: the 60-dps run is only a diagnostic).**
`asin(0.38) < π/8` because `sin(π/8) = √((1 − √2/2)/2) = 0.3826834… > 0.38` (equivalently
`√2 < 1.4224` ⟸ `2 < 2.0232`). Hence `16 asin(0.38) < 2π` and

> `w_min = 2π − 16 asin(r) ≥ 2π − 16 asin(0.38) > 0`.

A quantitative elementary bound: `asin(x) ≤ x + x³/6 + 3x⁵/40 + 15x⁷/336` for `x = 0.38` gives
`asin(0.38) < 0.3898 < 0.39`, so `w_min > 2π − 16·0.39 = 0.043185… > 0` (the last step uses the
rational bound `sin(0.39) ≥ 0.39 − 0.39³/6 > 0.38`, an alternating-series estimate). The 60-dps
evaluation `w_min = 0.0464445635914…` is reported as a **numeric diagnostic only**, not as a certificate.

**(L3) Bootstrap.** Applying (L2) again to the eight others: `Δ_i ≤ 2π − 8 w_min = 5.9116287984…`, so

> `w_min ≤ Δ_i ≤ min(2 asin r, 2π − 8 w_min)`.

**(L4) Legal domain (wording corrected, lead f657c6a6).** `{Δ ∈ R⁹ : Σ Δ_i = 2π, 0 ≤ Δ_i ≤ 2 asin r}` is
an **8-dimensional compact simplex slice**. The sum constraint together with the caps **already force**
`Δ_i ≥ w_min` (that is exactly (L2)); there is **no additional thin layer** `Δ_i < w_min` — the earlier
sentence claiming one was self-contradictory and is withdrawn. Consequently:
* essential positivity (`Δ_i > 0`) is **automatic** on this domain (indeed `Δ_i ≥ w_min > 0.043`);
* the domain is nevertheless **only a relaxation** — not because of any boundary layer, but because the
  remaining geometry (switch/hub conditions, central structure) is not yet encoded.

Nonemptiness of the box-constrained slice is automatic as well: `9 w_min < 2π < 9·2 asin r`
(`9·0.043185 = 0.3887 < 6.2834`; `9·2 asin(0.38) = 7.0163 > 6.2832`; the latter is the elementary
`2 asin(0.38) > 2·0.38 = 0.76` ⟹ `9·0.76 = 6.84 > 2π` ✓).

## 2. What is *not* yet included (corrected, per lead f657c6a6)

* **Deleted (was H2(i), wrong).** "The hub covering a switch arc must lie within `r` of the arc's
  endpoints" is **false** and is removed: strict hubs have `|h| < ρ = 1 − r` and therefore **cannot cover
  any point of the unit boundary** (`|h − U| ≥ 1 − |h| > r`). No hub-side endpoint condition exists in
  this form.
* **Still missing (honest).** The switch/hub coupling and the central (two-site) structure are not encoded
  here; the polytope above is a *relaxation* of the legal angular domain.
* **Not attempted.** No central-span polytope is invented; no SOCP optimisation, no feasibility claim.

## 3. Literature interface (per lead: reuse existing lit notes first, then a precise search; no novelty claims)

**Repo-side literature notes (reused, not re-derived).**
* `lead/CIRCLE-PATTERN-LITERATURE.md`: Bobenko–Springborn (Trans. AMS 356 (2004) 659–689) gives a strictly
  convex Euclidean functional in log face radii **for fixed circle intersection angles**, with no theorem
  minimising a *maximum* covering radius over **free** intersection angles; Springborn (arXiv:math/0603097)
  shows coherent triangle angles do not glue without a scale-compatibility criticality — i.e. exactly the
  kind of non-linear interface that a naive angular reduction would drop. Both notes explicitly warn
  against concluding global uniqueness/symmetry from fixed-angle uniqueness. **Neither covers the
  fixed-boundary-site minimax SOCP reduction asked here.**
* `lead/VORONOI-BOUNDARY-REDUCTION.md` + `lit2/fejes-toth-2005-lemmas.md`: the Dirichlet-cell /
  boundary-capacity method (Fejes Tóth 2005) is the established local-capacity tool for `n = 8,9,10`;
  the lead's own notes mark such uses as elementary specialisations, **no novelty claim**.
* `lead/NO-FOUR-RING-COMMON-POINT.md`, `lead/RING-LOCALITY.md`: boundary-capacity mechanism again, with
  the explicit instruction not to claim a literature theorem is disproved and not to claim novelty.

**External search: route failed.** Two `web_search_exa` calls for "minimax covering of the circle by
equal disks, fixed boundary sites, SOCP dimension reduction / candidate optima" returned
`error: fetch failed` (infrastructure, not a negative result). Per the retry-then-change-route rule I
stopped after the retry; **no new external search results are claimed**. The targeted queries to re-run
when the route is available: (i) "minimising the maximum of a convex function over a polytope, number of
optimal candidates"; (ii) "covering the circle by equal disks: finitely many candidate configurations";
(iii) "second-order cone representable minimax covering with fixed sites".

**Consequence for this note.** Everything in §1 is elementary analysis of the angular domain (disk-arc
geometry + the AM-GM minimum of `f(c) = (1 + c² − r²)/(2c)`), presented as an interface fix, **with no
novelty claim and no literature-based authority**; the SOCP dimension-reduction question is left open and
must be searched properly before any claim.

Repro:
```
py -3 -B -X utf8 research-2026/team-current/r20-geometry/angular_domain_coverage.py
```
