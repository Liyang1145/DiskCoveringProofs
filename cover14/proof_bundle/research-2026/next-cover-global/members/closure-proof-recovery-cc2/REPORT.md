# Boundary closure recovery — analytic accept/reject on the two elementary arguments

Scope of this report: ONLY the two items requested.
 (P) `lead/BOUNDARY-CYCLICITY-PROOF.md`  (C1252) — exact ray-order argument + closure identity
 (N) `lead/BOUNDARY-ANCHOR-NORM-CONSTRAINT.md` — polynomial norm-cone interface
Context read for the interfaces (not audited here): `OWNER-COUNT-UNIFICATION.md` (C1171),
`BOUNDARY-ANCHOR-OUTSIDE-EDGE.md` (C1250), `CYCLIC-POLYGON-CLOSURE.md` (C1251),
`BOUNDARY-ANCHOR-PARAMETRIZATION.md`, `BOUNDARY-CYCLICITY-INTERFACE.md`,
`normalized_boundary_control.py`+json (20 correct normalized controls).
No numerical-optimization or raw-perturbation hunt was run; previous member files that allege
counterexamples from unnormalized sites were not used as bearing evidence.

## VERDICT SUMMARY

| item | verdict | grade |
|---|---|---|
| (P) ray order `A_- < u < b < v < A_+` inside the inward semicircle | **ACCEPT (valid)** | proved-exact, needs 3 named side-conditions (all supplied by C1171/C1250) |
| (P) unwrapped closure `2γ_A + δ_(u,A) + δ_(v,A) + (θ_u+θ_v)/2 = π` follows | **ACCEPT (valid)** | proved-exact |
| (N) cone inequality `cos γ_A ≥ k(a) = (a²+U²)/(2a)` incl. `γ_A < π/2` strict | **ACCEPT (valid)** | proved-exact |
| (N) real-face coupling `cos γ_A = (a−R cos β)/D` and the polynomial form | **ACCEPT with a named interface caveat** | proved-exact; `β` MUST be the angle at the site u inside triangle `u-A-O` (see (N3)) |

Nothing in either file is rejected.

## (P) RAY-ORDER ARGUMENT — accepted, with the exact sentences it rests on

Setting. `A ∈ S¹` shared boundary switch of owners `u,v`; `A_-`, `A_+` the two adjacent anchors
(so `u` owns the arc `A_-A`, `v` owns `AA_+`); `b =` inward bisector ray `AO`, `O` the real-face
circumcentre inside the disk; all sites strictly inside the disk (norm `≤ s = √(1−U²)`,
`U ≤ 1/3`), owner arcs positive with `θ ≤ 2 asin U < π`.

Evaluation of the five steps, in the file's own terms:

1. *"The four rays Au, Av, AA_-, AA_+ lie in the open inward tangent halfplane at A, an angular
   interval of length pi."*  **Valid.** For any point `x` of the closed disk, `(x−A)·(A−0) ≤ 0`
   with equality iff `x = A`; the four rays end at points ≠ A. `|A_+ − A| > 0` because anchors
   are distinct, and `u ≠ A` because `|A−u| = a ≤ U < 1 = |A|`. The two endpoint rays
   `AA_-`, `AA_+` are chord directions of a proper chord; the interval between them inside the
   semicircle is `[0,π]` and its measure is **exactly π** — this is the Thales step
   (`A_-` and `A_+` are on the circle and `∠A_-AA_+ = π/2`, so the two rays are `π` apart). This
   exactness is what removes the `mod 2π` ambiguity.
2. *"In that interval the bisector line has exactly one ray b."*  **Valid.** The bisector line
   through A meets the semicircle; one ray is inward because `O ∈ int D` (C1250). The rays to
   `A_±` point into the open interior of the halfplane `H_u = {x : |x−u| ≤ |x−v|}`:
   `(A_± − A)·(A−0) > 0` (proper chord), and every interior point of that chord direction is
   strictly on the origin side of the bisector line, so it lies in `int H_u` / `int H_v`.
   **This sentence is the one place that needs the ownership structure**: it uses that `A_-`
   and `A_+` are the *genuine* adjacent anchors of the owner cycle. That is exactly what
   `OWNER-COUNT-UNIFICATION.md` §3 supplies at inflated radius `R_ε` (positive-length arcs,
   every switch has exactly two owners, finitely many tie points). Without that cleaning the
   sentence can fail for an arbitrary site set — I exhibit that numerically below, and it is a
   non-cover artifact, not a counterexample.
3. *"The nearest-halfplanes place AA_- and Au on its u-side, and AA_+ and Av on its v-side. Thus
   b lies between the two chordrays."*  **Valid.** `A_- ∈ H_u`, `A_+ ∈ H_v` and `u ∋ A ∈ W_u`,
   `v ∋ A ∈ W_v`; `A ∉ b` because `A ≠ u,v`, so `b` separates the two sides; `b` lies in the
   interval and therefore strictly between the two chord rays. Convexity of `H_u` is not needed.
4. *"The unitcircle minus the minorarc A_-A lies on the origin-side of chord A_-A; in particular
   A_+ lies there. By §1, u also lies on that side. Within the inward angular semicircle, this
   implies Au is on the b-side of AA_-."*  **Valid, and the two halves are logically separate:**
   (i) `A_+` origin-side of chord `A_-A` — the chord (a proper secant, since `A_-A` is a minor
   arc, `θ_u ≤ 2 asin U < π`) is inside the closed disk and meets the circle only at `A_-,A`;
   every other circle point is on the origin side. (ii) `u` origin-side of that chord — `u` is
   in the open disk (`‖u‖ < 1`) and §1's norm bound gives `n·u < cos(θ_u/2)`, i.e. `u` strictly
   inside. The conclusion "`Au` on the `b`-side of `AA_-`" then follows inside the semicircle.
5. *"Combining this with Au being on the AA_--side of b places Au between AA_- and b"; same for
   Av; "The ray order is therefore AA_-, Au, b, Av, AA_+, or its reverse."*  **Valid.**
   `Au ⊂ int H_u` and `b` is the bisector line, `A_+ ∈ H_v`, so `Au` lies on the `A_-` side of
   `b`; with step 4 this pins the interval. The "or its reverse" is the correct hedge only when
   the full anchor cycle runs clockwise; with `A_- ,A, A_+` labelled in the cycle's own
   orientation the order is definite.

Consequence (accepted): the star angle at `A` decomposes as
`δ_(u,A) + 2γ_A + δ_(v,A)`, and the anchor-polygon interior angle at `A` between the rays
`AA_-` and `AA_+` equals `π − (θ_u+θ_v)/2`. Reason, done independently of the file:
with `p = A_-`, `x = A`, `n = A_+` on the circle in cyclic order, the signed turn at `x` is half
the arc from `p` to `n` through `x`, i.e. `(θ_u+θ_v)/2` (this is the triangle-exterior-angle
theorem applied to the three chords, and it holds for obtuse/non-convex vertex configurations;
the role of §2 is precisely to guarantee the turn is measured inside the semicircle, so no
`2π` term enters). Total-angle check: `Σ_A [π − (θ_u+θ_v)/2] = qπ − 2π`. Hence

  **`2γ_A + δ_(u,A) + δ_(v,A) + (θ_u+θ_v)/2 = π` unwrapped, with no branch ambiguity.**

Special cases / scope (accepted as written): `θ_u = 0` or `θ_v = 0` (equal anchors) is not
covered by the strict positive-arc representation; it is handled by deleting zero-length arcs
and keeping the compatible limiting angle variables, exactly as §4 says. `atan2(0,0)` is never
used. `O` need not lie in either owner wedge triangle and `h_O` may have either sign (C1250).

## (P) NUMERICAL READING (not proof; only to locate the exact scope)

`strict_probe2.py` (this directory) enumerates random site sets and keeps only those that
satisfy **all** premises at once: `ρ ≤ 1/3`, every `‖site‖ < √(1−ρ²)`, every owned arc
`≤ 2 asin ρ`, single owner per arc verified at 5 interior samples, and the two owners of each
arc exactly the two nearest sites at the switch.
  - 7,589 accepted configurations, `q ∈ [11,21]`, `ρ ∈ [0.2491, 0.3333]`, max owned arc `0.6617
    ≤ 2 asin ρ = 0.6797`.
  - unwrapped closure residual ≤ `5.9e−13` over all of them; inner-chord-side violations 0;
    all `h_A < 0` (max `−0.0745`); inner-chord margin `cos(θ/2) − c·p > 0` with min `1.1e−2`.
  - residual "violations" of my ray-order screen occur only in configurations where the switch
    list contains a **phantom switch** (a site nearest at an isolated boundary point only): the
    printed record there has span `≈ 3.54` instead of `π` together with `(A_-−A)·A > 0` and
    `(A_+−A)·A > 0`, i.e. the "previous anchor" is not on the same arc. Those configurations are
    outside the premise set (no positive-length owner arc chain), so they are **not**
    counterexamples; they are the exact reason step 2 above is stated as requiring C1171's
    owner normalization.
  - `normalized_boundary_control.py` (lead, 20 controls with guaranteed cover radius, inner-root
    replacement and outward clip, i.e. inside the norm cap) gives `max|residual| = 1.33e−15`,
    `min` inner-chord margin `2.46e−6`. Reproduced: `py -3 -B
    research-2026/next-cover-global/lead/normalized_boundary_control.py`.
  - I could not build a *genuine* 14-site cover whose boundary facets have their second
    Voronoi vertex inside the disk at the existing catalogue (`R ≤ U` empirically forces
    `ρ ≲ 0.28`), so the "R ≤ U" family is not exercised densely here. That is a method limit of
    my probe, not a gap in (P): (P) does not use `R`.

## (N) NORM-CONE DERIVATION — accepted, with one named interface caveat

Setting. Fixed threshold `U`; after inner-root normalization and C1171 clipping every site has
`‖c‖ ≤ s = √(1−U²)`. `A ∈ S¹` shared anchor, `a = |A−u| = |A−v| ≤ U`, `2γ_A = ∠uAv`.
Define `d_u := (A−u)/a` (**from the site toward the anchor**), so `u = A − a d_u`.

Step-by-step:

(N1) `A·d_u = (‖A‖² + a² − ‖u‖²)/(2a) ≥ (1 + a² − s²)/(2a) = (a² + U²)/(2a) =: k(a) = a/2 + U²/(2a)`.
   Exact identity: `1 + (a−U)²/(2a) = k(a)`, so `k(a) ≥ U` with equality iff `a = U`, and
   `k'(a) = (a²−U²)/(2a²) ≤ 0` on `(0,U]`. **Valid.**
(N2) With `A=(1,0)`, `d_u = cos ψ·A + sin ψ·A_⊥`: `A·d_u = cos ψ` and
   `‖u‖² = 1 + a² − 2a cos ψ`. Hence the cap `‖u‖ ≤ s` is **equivalent** to `cos ψ ≥ k(a)`:
   the cone of admissible directions has half-angle `acos k(a)` about the **inward** radial
   `−A`. Also `a ≥ 1 − s` (reverse triangle: `‖u‖ ≥ |1 − a|`, `‖u‖ ≤ s`). **Valid.** (In the
   file this appears as `A·d_u ≥ k(a)` with the comment that `d_u` is a unit vector; the
   direction of the cone is not written down, and both `A·d_u ≥ k` and the equivalent
   "half-angle `acos k(a)`" are correct. I flag the direction explicitly because two of my own
   intermediate sketches got it backwards; the file's algebra is right.)
(N3) Two directions, each within `acos k(a)` of `−A`, have mutual angle `≤ 2 acos k(a)`; hence
   `2γ_A ≤ 2 acos k(a)`, i.e. `cos γ_A ≥ k(a) ≥ U > 0`, i.e. **`γ_A < π/2` strict**, and the
   bound is attained (both directions on the cone boundary with the bisector radially inward:
   `ψ_u = −ψ_v = ±acos k(a)`, then `‖u‖ = ‖v‖ = s` exactly). **Valid, sharp, not improvable.**
(N4) Real-face coupling. Let `O` be the real-face circumcentre, `R = |Ou| = |Ov|`,
   `D = |A−O|`, and `β` the angle **at the site `u` inside triangle `u-A-O`**, i.e.
   `β = ∠(uO, uA)` (one of the two face angles at `u`, the one formed with the anchor ray).
   Law of cosines on `u-A-O`: `D² = a² + R² − 2aR cos β`, and
   `cos ∠(uA,uO) = (a² + D² − R²)/(2aD) = (a − R cos β)/D`. **Valid** — verified symbolically for
   random `a,R,β` (residual `≤ 1.5e−14` over 2·10⁴ triangles) and by identity
   `(a−R cos β)/D ≡ (a²+D²−R²)/(2aD)`.
   **CAVEAT (interface):** the same symbol `β` in this file and in the face ledger
   (`γ_f + γ_A = π − β`, `R_f sin γ_f = a_e sin γ_A`) is the *paired angle at the site in the
   other convention* — with the two rays running to the two endpoints of the face edge. In the
   boundary-edge restriction (`A` on the line through `u,v` with `A` exterior to `uv`), the wedge
   between `u→A` and `u→v` is `π`, which is degenerate, so the formula `(a − R cos β)/D` and the
   ledger relation cannot both use one and the same `β`. The file's own algebra is correct if
   `β` is read as `∠(uO,uA)`; the interface must say which. This is the only real defect found
   in (N), and it is a naming/interface defect, not an algebraic error.
(N5) Polynomial form. Substituting `cos γ_A = (a−Rc)/D` with `c = cos β` into
   `cos²γ_A ≥ k(a)²` gives, after multiplying by `4a²D² > 0`,
   `4a²(a−Rc)² ≥ (a²+U²)²D²` together with the unsquared sign condition `a − Rc ≥ 0`.
   **Valid, and the necessity direction is exactly what the file claims**: it is *implied* by
   the norm cone, so it is a necessary condition; it is not sufficient for realization.
   The file's warning that "the square is legitimate only WITH the unsquared nonnegative sign"
   is correct and necessary: without `a − Rc ≥ 0` the squared inequality is weaker and admits
   spurious branches. At `D = 0` the polynomial inequality degenerates to `(...)² ≥ 0`, i.e. is
   vacuous, and `cos γ_A = (a−Rc)/D` is `0/0`; retaining the limiting angle variable is the only
   correct treatment — exactly as stated.
(N6) Normalization `a = Uy`, `R = Ux`. `D² = a² + R² − 2aRc` becomes `D² = U²(y²+x²−2xyc)`;
   the two sides of the polynomial inequality are `4U⁴y²(y−xc)²` and `U⁴(1+y²)²·U²(y²+x²−2xyc)`,
   so after dividing by `U⁴`:
   **`4y²(y−xc)² ≥ U²(1+y²)²(y²+x²−2xyc)`** together with `y ≥ (1−√(1−U²))/U` and `y − xc ≥ 0`.
   **Valid** (verified symbolically; note the factor `U²` on the right, since
   `u²(1+u²)²·u²(...)` — the file's "4y²(y−xc)² ≥ U²(1+y²)²(y²+x²−2xyc)" is the correct
   scaled form).
(N7) The stronger-than-`k≥U` statement is correct: `k(a) ≥ U` with equality only at `a = U`;
   the "candidate all `a=U`" line is fine but should not be read as saying `k(a) = U` is
   typical, and `a = U` is admissible only when `2U ≤ s` (i.e. `U ≤ 1/√5`), which holds at
   `U = 1/3` (`2U = 0.6667 ≤ 0.9428`). Endpoint behaviour: `k(1−s) = 1`, so `γ_A → 0`; for
   `a > 1−s`, `k(a) < 1` gives `γ_A > 0`.

### (N) numeric reading (not proof)
  - symbolic identities (N1),(N2),(N4),(N5),(N6): exact, residual 0 (`audit_v4.py`, `sym_normcone.py`).
  - brute force with **all four premises** (`|u|,|v| ≤ s`, `|Au|,|Av| ≤ U`, sites built directly
    from the cap): 38 767 samples, **0 violations**, min slack `cos γ_A − k(a) = 4.2e−3`
    (`final_elementary_check.py`). The worst-case record is `a = 0.0575`, `k(a) = 0.9185`
    (the near-tight `a → 1−s` end).
  - An earlier screen I ran (47548 samples) reported 688 "violations"; on inspection they came
    from triples where **`|Av| ≠ |Au|`** (only one owner within `a` of `A`), i.e. they are not of
    the file's form — a premise mismatch in my screen, not a counterexample. Reported here
    because the same mistake is easy to make when re-testing this constraint: the inequality is
    stated for the *shared* anchor radius `a` of both owners.

## Minimal open points (not counterexamples)

1. (P) The ray-order proof uses C1171's cleaning at inflated radius implicitly, through "`A_-`
   and `A_+` are the adjacent anchors of the owner cycle". If one wants the statement for an
   *arbitrary* legal site set (with phantom switches / sites owning single boundary points),
   that sentence is false as stated and the argument must be restricted to positive-length
   owner-arc configurations (or restated with zero-length arcs as limits). No repair is needed
   for C1252's stated domain.
2. (N) The symbol `β` must be disambiguated between the two conventions (see (N4) caveat).
   `BOUNDARY-ANCHOR-NORM-CONSTRAINT.md` is correct under the `∠(uO,uA)` reading.
3. (N) `a = U` (the saturation line used for the "candidate all `a=U`" case) requires
   `2U ≤ s ⇒ U ≤ 1/√5`; fine at `U = 1/3`, but the file does not state this side condition.

## Files
- `audit_v4.py` — symbolic chain (A), angle coupling (B), endpoints (C), brute-force cone (D)
- `sym_normcone.py` — independent symbolic re-derivation of (N1)–(N6)
- `final_elementary_check.py` — correct-premise brute force for the cone + `a=U` feasibility
- `beta_identification.py`, `final_consolidated.py`, `check_anglecoupling2.py` — β-identification
  diagnostics (these two last ones contain **superseded wrong β configurations**, kept only as
  the audit trail of the interface defect; do not cite their beta columns)
- `strict_probe2.py` — premise-complete random probe for (P), incl. the phantom-switch record
- Repro: `py -3 -B <script>` from this directory; lead's control:
  `py -3 -B research-2026/next-cover-global/lead/normalized_boundary_control.py`
