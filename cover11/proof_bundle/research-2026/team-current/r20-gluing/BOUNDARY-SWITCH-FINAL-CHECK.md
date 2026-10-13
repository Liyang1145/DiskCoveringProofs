# BOUNDARY-SWITCH-FINAL-CHECK — independent algebra check of `lead/BOUNDARY-SWITCH-ANGLE-PROOF.md` §§1–4

**Lane**: r20-gluing (cline2-r23-gluing), sole writer here. Read-only audit of the lead note (lead
files untouched). **No claim, no sub-agent, no numerics.** γ-location discipline observed: γ is the
angle **at the site** (L9), and this note's §2 is read that way.

## §1 — the exterior-side sign: algebra reproduces exactly

Frame at `m := (c+d)/2`, `a := |c−d|/2 > 0`, orthonormal `(e, n)` with `e ∥ cd` and `n` toward the
owned switch `U`. Write `c = m − ae`, `d = m + ae`, `U = m + ℓn` (`ℓ > 0` because `m ∈ int D`, and the
two bisector exits are distinct), and the first interior Voronoi vertex `z = m + tn`, `t < ℓ`.

* Equidistance at `z` for the third site `k = m + pe + qn`:
  `|z−c|² = t² + a²` and `|z−k|² = p² + (t−q)²` ⇒ `p² + q² − a² = 2tq` — **matches the note** ✔.
* Nearest-site validity at `U`: `|U−c|² = ℓ² + a²`, `|U−k|² = p² + (ℓ−q)²`, so
  `|U−k|² − |U−c|² = p² + q² − a² − 2ℓq = 2q(t−ℓ)` — **matches the note** ✔.
* `t < ℓ` and (at a two-site switch, which is what the cellulation gives — VORONOI §3/R2 proves the
  other sites are *strictly* farther) the left side is `> 0`, hence `q < 0` strictly: `k` lies on the
  side of the chord line *opposite* `n`, i.e. the faces are interior. The sign conclusion is therefore
  **derived**, not asserted ✔. The cocircular addendum is also correct: every other incident site obeys
  the same two relations with its own `(p',q')`, so all of them have `q' < 0`; any refinement keeps the
  faces interior ✔.
* Positive entering-edge length needs transversality (the bisector meets `∂D` at distance
  `≤(|c|+|d|)/2 ≤ √(1−r²) < 1`, VORONOI §3/R2) plus the strict two-site tie; then the clipped edge has
  positive length ✔. The note's phrase "strict separation from other sites" is one of the two
  ingredients; the other (secancy) is available but not cited in that line. Minor, not an error.

## §2 — the acute switch angle: verified

In the isosceles triangle `(c, U, d)` the altitude to the midpoint `m` gives right triangles with legs
`ℓ` (at `U`) and `a` ⇒ `tan b = a/ℓ`, `b = atan2(a, ℓ) ∈ (0, π/2)`, `σ² = a² + ℓ²`, and the base angle
at either site is `π/2 − b` with `tan(π/2 − b) = ℓ/a`. **All four claims match** ✔. The statement that
the older larger signed domain is a relaxation (not a contrary premise) is consistent with §1 ✔.

## §3 — arc angle and ray order: (i),(ii) verified; the algebraic alternative is not self-verifying here

* Half-plane: for `W ∈ ∂D` with `|W−c| ≤ r`, `c·W ≥ (1 + |c|² − r²)/2` ⇒
  `c·(W−c) ≥ (1 − |c|² − r²)/2 ≥ 0` — **exactly the note's inequality**, and the sign is the
  inward-root bound `|c|² ≤ 1 − r²` ✔.
* Strict monotone polar angle: `d/dθ arg(W−c) = (1 − c·W)/|W−c|² ≥ (1 − |c|)/|W−c|² > 0` — **matches** ✔.
  Together with connectedness of the owned arc this gives a single swept angle `α`, and the outward
  half-plane gives `α ≤ π`; so "no major angle from endpoints alone" is correct ✔.
* Ray-order identity `ι + γ_l + γ_r + α = 2π` then `α + Σ_f A_fc − b_l − b_r = π`: this is the
  derivation I already re-derived independently in `AREA-IDENTITY-AUDIT.md` §3 (rays
  `c_{i−1}, U_{i−1}, U_i, c_{i+1}` × four disjoint sectors; `ι = Σ_f A_fc` from the faces tiling
  `int P` at the site), and §1 supplies the disjointness of the exterior wedges. **Verified** ✔.
* **Wedge computation — now supplied by the source, and I verified it.** `θ_e = π − a_e − b_e` and the
  counting. With the site at `(0,0)` and its neighbour at `(2s,0)`, the primal edge lies on `x = s` with
  endpoints `(s, −s·cot A)`, `(s, s·cot B)`, `A, B ∈ (0,π)` the opposite angles of the two incident
  triangles. The ray directions from the site are `atan(−cot A) = A − π/2` and `atan(cot B) = π/2 − B`,
  using `atan(cot A) = π/2 − A` throughout `A ∈ (0,π)` (valid since `cot A = tan(π/2 − A)` and both sides
  lie in the principal branch). The wedge spanned through the neighbour direction `0` therefore measures
  `(π/2 − B) − (A − π/2) = π − A − B = θ_e` ✔, obtuse angles included. An artificial (zero **primal**
  Voronoi segment) diagonal has `A + B = π`, so `θ_e = 0` ✔. Counting: the `d−1` refined triangles have
  total angle sum `(d−1)π`, of which `ι` sits at the site, leaving `(d−1)π − ι` in their "not-at-c"
  angles, each incident triangle contributing its two non-c angles once ✔. **My earlier "completeness
  gap" is closed** — the algebraic route is now self-contained as well as redundant with the ray-order
  proof.

## §4 — area accounting: formulas check against standard identities

* Interior dual edge, opposite angles `a, b`, **dual site distance** `d` (strictly positive — see the
  correction below): signed circumcentre offsets `(d/2)cot a`, `(d/2)cot b`, so the paired piece is
  `(d²/4)(cot a + cot b)` — **matches**; Delaunay's empty-circle condition gives `a + b < π`, hence
  `cot a + cot b = sin(a+b)/(sin a sin b) > 0`, i.e. the combined term is *nonnegative* even when one
  angle is obtuse ✔. **Correction (lead): what vanishes for an *artificial* diagonal is the PRIMAL
  Voronoi segment length, not `d`.** There `a + b = π` (cocircular quadruple), so
  `cot a + cot b = 0` and the paired piece is `0` ✔ — the source states this correctly
  ("artificial zero-primal-length diagonals contribute zero"); my earlier phrasing "`d = 0`" was my
  error and is withdrawn.
* Reassembly: the signed circumcentre pieces of a face sum to its ordinary area
  `2ρ² sin A sin B sin C` (circumradius form; obtuse faces included since the pieces are signed) ✔.
* Switch piece: `σ² sin(2b)/2 = (a²+ℓ²)·(a/σ)(ℓ/σ) = aℓ` — exactly the triangle `(c, U, d)`'s area
  `½·2a·ℓ` ✔; ring cap `σ_lσ_r sinα/2 + (w − sin w)/2` = the site-arc triangle plus the unit circular
  segment of angle `w` ✔.
* "All genuine endpoint radii are positive; the closed zero-radius/zero-angle domains only enlarge the
  range" — correct relaxation wording ✔.

## Verdict (concise)

§1 (derived exterior sign), §2 (acute `b`, `γ = π/2 − b`, `σ² = a²+ℓ²`), §3(i),(ii), §3's now-explicit
wedge computation and §4's formulas are **verified by explicit algebra**; the ray-order identity is
verified and consistent with my independent `AREA-IDENTITY-AUDIT.md` §3 derivation. The one item I had
listed as a completeness gap (the algebraic wedge route `θ_e = π − A − B` and the counting) is **closed
by the source's added calculation, which I checked** (including obtuse angles and `θ = 0` for artificial
diagonals), and my "`d = 0`" slip for artificial diagonals is corrected (the vanishing quantity is the
**primal** Voronoi length; `a + b = π` ⇒ `cot a + cot b = 0`). No contradiction with any line of §§1–4
was found. No claim registered; the original global goal remains open pending assembly, as stated.
