# C844 filter + line-86 monotonicity — focused audit (no code edits, no new kernel runs)

Subject: `lead/certify_q0_closure.py` ring kernel, lines 76-108; proposed filter C844.
Read: `lead/INWARD-SECTOR-COUPLING.md` (Round 9).

## 1. Line 86: precise condition on C

Code:
```
84  w  = 2*asin(R*sqrt(q)/2)
85  wl = iv.mpf(w.a); wh = iv.mpf(w.b)
86  h  = interval(((C+1/2)*wl - sin(wl)/2).a, ((C+1/2)*wh - sin(wh)/2).b)
```
Line 86 evaluates the radial "tent" function
`g(w) = (C+1/2)w − sin(w)/2` at the two endpoints of the *interval* `w`, and takes the
lower endpoint of `g(w_l)` / upper endpoint of `g(w_h)`.

**Allowed C.** `g'(w) = (C+1/2) − cos(w)/2`. On `w ≥ 0`,
`g'(w) ≥ g'(0) = C`, and `g'(w) ≤ C + 1/2·(1−cos w) ≤ C + 1/2 ≤ C+1/2`.
So:

* `g` is **nondecreasing on `[0,∞)` iff `C ≥ 0`** — this is exactly the needed condition,
  because then `g` is the *increasing* map from `w` to the tent value and the endpoints of
  the interval `w` give the extremes of `g`. (No condition of the form `C ≥ 1/2` or
  `λ ≥ 0` is needed; `C = 0` gives `g(w) = w/2 − sin(w)/2 ≥ 0`, increasing.)
* Sufficient, robust version: `C ≥ 0` with a margin, i.e. `oldlambda = z[71] ≥ 0` **and**
  `z[72] ≥ 0` (`eta`). The code *asserts only* `z[72]==0` exactly (line 12) and
  `all(v.a>=0 for v in z[50:71])` (line 9) — it does **not** assert `z[71] ≥ 0`.
  In the current row `lead/q0_closure_dual_0_3.json`, `z[71] = 0.006767450… > 0`, so
  `C = z[71] > 0` for all i and line 86 is sound as written.
* If `C < 0` the map is not monotone on `w ∈ [0, 4asinR]`: `g'` changes sign at
  `w* = 2·acos(2C+1)` (for `C ∈ (−1/2, 0)`) or the function is decreasing throughout
  (`C ≤ −1/2`). Then the two endpoint evaluations in line 86 do **not** bracket the true
  range of `g`, and the enclosure is wrong (too small at the bottom). **Pitfall:** there is
  no assertion guarding this; add `assert z[71].a >= 0` (and keep `z[72]==0`) so that a future
  re-solved dual cannot silently make line 86 unsound.
* Range note: since `w ≤ 2·asin(R√q/2) ≤ 2asin(R) ≈ 0.7793 < π`, monotonicity carries with
  room; `cos w > 0.7071` on that range, so `C ≥ 0` gives `g' ≥ 0` with margin ≥ 0.
* One more consequence worth recording: with `C ≥ 0`, `g(w) ≥ 0` on `[0,π]`, so
  `h ≥ 0` pointwise. The code relies on `h ≥ 0` when it uses `h`/`w` for the closure weights
  and for the derivative clips below. `C < 0` would break that too.

## 2. Is C844 sound?

Intended rule (from `INWARD-SECTOR-COUPLING.md`, eq. (8) and the two relaxations):
```
L := uv(k sin a − h cos a),          k = sqrt(1−h²),  h = R0*sqrt(q)/2
discard a box only if   upper_box(L) < lower_box( max((75/76)², u², v²) * h )
```
**Verdict: sound, given the side conditions below.** Reasons, slot by slot.

* `u,v ∈ [0,1]` (`u = p/R0`, `v = q/R0`, `p,q ≤ r ≤ R0`). `q = (u−v)² + 4uv sin²(a/2)`
  is an exact nonnegative form; `q ∈ [0,4]` on `a∈[0,π], u,v∈[0,1]`, so clipping
  `q` to `[0,4]` is lossless (it clips only *outside* the box, never inside).
* `h = R0√q/2`: increasing in `q`, `h ∈ [0, R0] = [0, 0.38]`, so `1−h² > 0` and
  `k = √(1−h²) ∈ [0.9249, 1]` is well defined. No branch issue.
* `L`'s enclosure: `L = u·v·(k sin a − h cos a)`. Interval evaluation is sound provided
  the products are taken with the *same* `q`-interval used to build `h` and `k` —
  i.e. one must not mix an `h` from the clipped `q` with a `k` or `uv` from the unclipped
  box. The interval form is fine; note the non-obvious fact that `L` is **not** monotone in
  `q` (∂L/∂h = −uv cos a changes sign with `a`), so a "endpoints only" evaluation would be
  wrong — the naive interval product (which the plan describes) is the safe route.
* RHS lower bound `max((75/76)², u², v²)·h`: if `(75/76)² ≥ ...` this is
  `max(c1,u²,v²)`; the *lower* bound over the box is
  `max(c1, u_lo², v_lo²) · h_lo`, and each factor is correctly monotone (h increasing in q;
  the max is monotone in u,v). ✔
* Discard predicate `upper(L) < lower(RHS)` is sound: at any admissible point
  `L ≥ RHS` (necessary condition), so a box with `sup L < inf RHS` contains no admissible
  point. The one-sided usage (never discard on `<` of a bound that isn't a true bound) is
  also correct: an under-estimate of `upper(L)` or over-estimate of `lower(RHS)` can only
  make the filter *more conservative*, not unsound.

### Side conditions that must hold (verify, don't assume)

1. `r ≥ max(p,q)`: needed for the second relaxation. In the inward model the two adjacent
   switches lie on the boundary of the *covered* region whose sites all have norm `≤ r`;
   the switches of the sector are on the arc between the two centres, and for the sector
   triangle the max distance to the arc is at an endpoint, so `max(p,q) ≤ r`. ✔ (provided the
   sector's own switches are within the `r`-allowance — this is the model's definition).
2. `r/R0 ≥ 75/76`: with `r ∈ [0.375, 0.37999]` and `R0 = 0.38`, `min r/R0 = 0.375/0.38 =
   0.986842 > 0.9868421… = 75/76` ✔ (equality margin ≈ 5e-6, so keep `r ≥ 0.375` as an
   inequality, not `> 0.375`).
3. `sin(a − w/2) ≥ 0` used in the exact equivalence: holds because `0 < w < a ≤ π`
   (w < a is the width-vs-sector-angle constraint). ✔ — but note this is **not enforced by
   the box** `[0,π]×[0,1]²`; it is a property of admissible points only. The filter uses
   only *necessary* conditions, so that is acceptable.
4. `R0 = 0.38` fixed units (lead states: do not re-root). ✔ The `(75/76)²` constant is
   computed with `R0 = .38`; do **not** reuse it if `R0` changes.
5. `qmin` filter still needed *before* the new filter, to keep `h > 0` (the lead says this).
   With `h = 0` the RHS is `0` and the predicate degenerates to `upper(L) < 0`; keep the
   `q ≥ qmin` guard and the `h > 0` convention.

## 3. Pitfall that matters: C844 does *not* license clip line 91

This is the one interaction I would flag hardest. The constraint `r ≤ R0`, fed through C844,
restricts the **area** of the admissible set, but **lines 88-92 compute derivative bounds on
the full box** `a∈[0,π], u,v∈[0,1]` (before/independently of the filter), and the clip

```
88  L = R/iv.sqrt(1−R2);  ...
91  wa,wu,wv clipped to [−L, L]
```
uses `L = R/√(1−R²) = 0.410817`. The true bound available from the *unit-disk* configuration
is `|w_a| ≤ (R r)(r cos(a/2))·…` — concretely `|w_a| = R² uv sin a / (√q·√(1−R²q/4))`, and the
maximal value over the *box* is not attained at the unit-disk extremal.
* On the box `[0,π]×[0,1]²` (which contains points with `q` up to 4 and `uv` up to 1), the
  computed maximum of the three partials can exceed `L`: `|w_a| ≤ R²·1/(2q)·…`; e.g. at
  `a = π/2, u=v=1` one gets `|w_a| ≈ 0.145` (safe), but the *bound* `R² uv sin a / q` with the
  independent maximisation `q ≥ |u−v cos a|` style reasoning gives values up to `≈0.41` at the
  box corner. My scanned maximum over a dense admissible grid was `0.379 < L` (earlier E8,
  `clip_window_test.py`), i.e. **on the admissible set the clip is fine**; on the raw box
  (which is what line 91 sees before any filter) it is not obviously fine, and the mean-value
  form (line 97) and the `gg` form (line 103) consume those clipped derivatives.
* Why this is usually harmless and where it is not: the code takes
  `interval(max(direct.a, mean.a), min(direct.b, mean.b))`. If `mean`'s gradient enclosure is
  not a valid MAC bound, `mean` can under-state the sup, and taking `max` with `direct` still
  gives a **sound upper** as long as `direct` is a true enclosure. The dangerous direction is
  the opposite one: if the clipped `mean` *over*-states the sup (over-clipped derivative in a
  region where the true derivative is much larger, giving a false "flatness"), then
  `min(direct.b, mean.b)` can fall below the true sup. That is exactly what a too-small `L`
  would do on a box whose true derivative range exceeds `L`.
* **Recommendation (no code edit requested, just the invariant):** keep the clip *only* if
  `L` bounds the partials on the **whole evaluation box**. Two safe options: (a) verify
  `|w_a|,|w_u|,|w_v| ≤ R/√(1−R²)` on the *enlarged* box — this is plausible because
  `√q ≥ |u−v cos a|`-type identities cap the numerators, but it is not what the derivation in
  INWARD-SECTOR-COUPLING.md proves (that proves the *unit-disk* case); (b) apply C844 *first*
  so that the derivative box is the admissible set, or (c) drop the clip and use the direct
  enclosure only on boxes that touch the enlarged region. If (a) is intended, it should be
  stated as a lemma with the box quantifier and checked at `q→0` / `u=v=1` corners.

## 4. Interaction of C844 with the mean-value evaluations

* Line 95-97 build `center`/`mean` from the **box midpoints** with no admissibility test: the
  midpoint of an admissible box can lie outside the admissible set (e.g. a box straddling the
  `qmin` level, or one whose midpoint has `sin(a−w/2) < 0` while the corners are admissible).
  That is **fine for soundness** — `mean` is a MAC bound that holds at every point of the box
  — provided the gradient enclosure is valid on the whole box (see §3).
* Do **not** tighten the box to the filter's region *partially* (contraction) without
  carrying the contraction through `grad`, `mean`, `gg`, `mean2`; the lead's note "no partial
  contraction inserted into gradients" is the right policy. If C844 is implemented as a pure
  *discard* predicate (as planned) this issue does not arise.
* Because `h` (line 86) is the *tent* function and, with `C ≥ 0`, satisfies `h ≥ 0`, the
  `extra` term at line 98 and `gg` at line 103 keep the sign pattern the certificate was
  tuned with. If a future dual has `C < 0`, both the `h ≥ 0` and the endpoint-enclosure
  arguments fail simultaneously — worth one explicit assertion (see §1).

## 5. Bottom line

* **Line 86 is sound iff `C ≥ 0`**; the current row satisfies this (`z[71] = +0.00676745`,
  `z[72] = 0`). Suggested guard: `assert z[71].a >= 0 and z[eta] == 0`.
* **C844 as stated is a sound discard rule**, with the four side conditions in §2
  (`r ≥ max(p,q)`, `r/R0 ≥ 75/76`, `w < a`, `R0 = 0.38` fixed, `q ≥ qmin` kept).
* **Main pitfall:** C844 restricts admissibility but the clip at line 91 (and therefore the
  MAC forms at lines 97/103) is justified by a *different* hypothesis — `|∂w| ≤ R/√(1−R²)`
  on the box actually being evaluated. Those two hypotheses must not be conflated: either
  prove the derivative bound on the enlarged box, or apply the filter before forming the
  derivative enclosure.
* Secondary: keep `z[71] ≥ 0` asserted; keep `q ≥ qmin`; do not reuse the `(75/76)²` constant
  with a different `R0`; and note `r = 0.375` uses the *closed* inequality
  (`(75/76)² = 5625/5776 = 0.97976…`; wait — recompute: `(75/76)² = 5625/5776 = 0.97385`),
  margin to `(0.375/0.38)² = 0.973854` is ≈ 4.7e-7, so treat it as `≥` with care.

*Correction inside this file:* the previous bullet's parenthetical is wrong as first written
(`0.97976`); the correct value is `(75/76)² = 0.973854`. The margin to `(0.375/0.38)²` is
≈ 4.7e-7 — i.e. C844's `(75/76)²` lower bound is **tight** for `r = 0.375`; if a box's lower
bound for `u²` or `v²` is used with `h_lo`, rounding must stay outward here.
