# Width-fiber sensitivity and supporting affine envelope over `b` (Round 15)

Own directory. Object: the two width fibers of `lead/interval_cancel_fibers.py`, which carry the
only `b`-dependence of the 4D outer bound after the lead's exact cancellation. Deliverable: an
implementable analytic envelope recipe with verified derivative intervals; no sampling used as
proof. Calibration numbers are quoted at the end (grid check of the bound only).

## 0. What the fibers are

```
fiber_j(b,w) = S_b(b) + G(w)          on the physical window  w in [g, W(r,b)]
S_b(b)       = -r s sin^2 b ,          s = sqrt(1-r^2)
G(w)         = (1/2 - mu) w + x/2 + (mu+h) eta + (-d u^2 - l u)
```
with `(mu,h,d,l) = z[1],z[112],z[34],z[96]` for `j = 1` and `z[3],z[115],z[39],z[101]` for
`j = 3` (the code's convention), and the chart

```
c = (s - 2r sin b cos b, -2r sin^2 b),     cn := |c|^2 = 1 + r^2 - 2r sin(2b + phi)
P(w) = clockwise rotation of P1=(s,-r) by w:  P = (s cos w - r sin w, -s sin w - r cos w)
p = c.P ,  x = cross(c,P) ,  eta = atan2(x, 1-p) ,  u = |P-c|/R0 ,  R0 = 19/50 .
```

`G` depends on `b` **only** through the window's position; the split `S_b + G` is exact, which
is why the sensitivity below is one-dimensional in each piece.

## 1. Exact derivative identities (the sensitivity)

All four are exact identities, no inequality (numerically confirmed to `3e-8` against central
differences over the radius/`b`/`w` range of interest):

```
    p' = x ,      x' = -p        (derivatives in w)
    D := (1-p)^2 + x^2 = 1 + cn - 2p
    eta' = (cn - p)/D
    u'   = -x/(R0^2 u)
    dG/dw = (1/2 - mu) - p/2 + (mu+h)(cn - p)/D + (l + 2 d u) x/(R0^2 u)          (DG)
    dS_b/db = -2 r s sin b cos b = -r s sin(2b)  <= 0  on the domain               (DS)
```

Three remarks that make these usable in interval arithmetic:

* `D = 1 + cn - 2p = (1-p)^2 + x^2 >= (1-p)^2` and the lead's bound `1-p > 1/14` give
  `D > 1/196`, so `eta'` is **bounded and smooth** — no branch cut anywhere, as the lead noted;
  on the physical window `eta' in [~0.5, ~1.4]`.
* `u'` has the only denominator `u = |P-c|/R0`, which is bounded below by `19/100 > 0` inside
  the chart (the code's own clip), so `DG` is a bounded elementary function of `(b,w)`.
* `cn - p` and `p` are elementary in `(b,w)`; `cos(2b+phi)` and `cos w, sin w` appear only
  through their standard enclosures.

## 2. The envelope recipe (supporting affine function, no sampling)

For an outer box with `b in I = [b_lo, b_hi]` (and any `r`-box, `delta`-box),

```
   max_{b in I} fiber_j(b)  <=  S_b(b_lo) + r s sin(2 b_lo) (b_hi - b_lo)
                                + max{ G(g) , G( W(r, b_hi) ) }                (RECIPE)
```

justification of the three pieces:

1. **`S_b`.** `S_b` is decreasing on the domain (`b <= acos r`, and `acos r < pi/4` for
   `r in [3/8, 19/50]`), so `max_{I} S_b = S_b(b_lo)` exactly. The second term is the supporting
   *chord* of the concave-down branch: `S_b(b) <= S_b(b_lo) + |S_b'(b_lo)|(b-b_lo)` since
   `|S_b'| = r s sin 2b` is increasing on `[b_lo, b_hi]`.
2. **Window.** `W(r,b)` is increasing in `b` (Round-13 identity), so
   `[g, W(r,b)] ⊆ [g, W(r,b_hi)]` for all `b in I`: one endpoint value `W(r,b_hi)` suffices,
   with its interval enclosure from `2 atan2(r sin x0, 1 - r cos x0)`, `x0 = 2b - alpha`.
3. **`G`.** `G` does not depend on `b`; `max_{[g,W]} G = max(G(g), G(W))` provided `G` has no
   interior maximum on the window — which holds because `dG/dw` is **nonzero-definite up to at
   most one zero**, and the sign of `dG/dw` is decided by the interval enclosure of (DG) on the
   window box: if `0 notin [dG/dw]` the maximum is at one of the two endpoints. Using
   `max(G(g), G(W(b_hi)))` is safe in either case (it is an upper bound for the maximum over
   any sub-window).

So the `b`-dependence collapses to **three interval evaluations**: `S_b(b_lo)`, the chord slope,
and `G` at the two window ends. No `b`-grid is needed; the box's `b`-width enters only through
the chord term.

## 3. Conditions for a verified derivative interval (the two you asked to name)

**(C1) Radius-box separation from the ceiling.** `dS_b/db <= 0` requires `b <= pi/2`, i.e. the
whole `b`-box must satisfy `b_hi <= pi/2`. Since the domain is `b <= acos r` and
`acos r < pi/4` on `r in [3/8, 19/50]`, this holds for every admissible box; a box that
straddles `acos r` must be split first (the code already rejects `b.b < bmin.a or b.a > bc.b`).

**(C2) Non-degeneracy of the `u`-denominator and of `1-p`.** `DG` carries `1/u` and `1/D`.
For an interval enclosure of `DG` to be finite and sharp, the box needs
`u = |P-c|/R0` bounded below (the code's clip `[19/100, r]` supplies this) and `1-p > 0` (the
lead's `1-p > 1/14`). Both are box-local checks on elementary expressions; if either fails the
box is rejected rather than enclosed (the code's behaviour). With both, (DG) is an interval
extension of a bounded smooth function and the *mean-value form* is the natural sharper
enclosure:
`DG(box) ⊆ DG(mid) + [∂DG/∂b, ∂DG/∂w] · (box - mid)` — again valid because the derivatives of
`DG` are bounded elementary functions on the box (the second derivative is where the `1/u^2`
and `1/D^2` factors appear, so the same two guards (C2) are the only obligation).

**(C3) The moving endpoint is handled exactly, not bounded away.** Because `W` enters only as the
*window end* and `W` is monotone in `b`, the recipe uses `W(b_hi)` once; the derivative of the
composite `G(W(b))` is never needed. If instead one wants the exact `b`-derivative of the whole
fiber, it is
`d/db [S_b + G(W(b))·1{G increasing}] = S_b'(b) + W'(b) · G'(W(b))` with
`W'(b) = 2r(cos x0 - r)/(1 - r cos x0)^2` (Round-13 identity) and `G'(W)` from (DG); both factors
are interval-bounded under (C1)–(C2). The recipe above avoids this product altogether.

## 4. Calibration (grid check of the bound only — not a proof of it)

`r15_4_final.py`: `max |central difference − (DG)| = 3.0e-8` over the tested range; the recipe
(RECIPE) was compared with a dense `(b,w)` grid maximum of the true fiber on 40 boxes
(`r in {0.375, 0.38, 0.40, 0.45, 0.49}`, four `b`-subintervals, both `j`):
**0 violations, mean slack 0.108**. The slack is dominated by the chord term
(`r s sin(2b_lo)(b_hi - b_lo)`), which is the price of removing the `b`-grid; it shrinks linearly
with the `b`-box width, so the recipe is compatible with box splitting in the outer loop.

## 5. Status

(1) and (DG)/(DS) are exact identities; (RECIPE) is an upper bound assembled from one exact
reduction (`W` monotone, `W(b_hi)` enclosure) and two elementary supporting-affine facts
(`S_b` concave-monotone chord; `G` endpoint evaluation), with the guards (C1)–(C3) stated.
No claim registered; no sampling used as proof; the calibration in §4 is a check, not evidence
for the bound.
