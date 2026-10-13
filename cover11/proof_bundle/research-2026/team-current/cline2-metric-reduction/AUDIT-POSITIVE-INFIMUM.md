# Audit of `lead/POSITIVE-METRIC-INFIMUM.md` (compact)

Verdict: the two technical claims I was asked to check are **correct**, the conclusion
`r_D(11) = inf_S R` follows, and one clause about "8 circle-ratio constraints" should be
dropped (it is the identity of C816, not a constraint). Details:

## 1. Strict boundary preservation (C464 at allowance `R`) — correct, one step to spell out

Let the site be `c`, let `u` be the unit normal of its chord (so the two radial roots are
`c - d u` and `c + d u` for the same `d > 0`), and consider a boundary point `P`. Expanding,

```
    |P - (c + d u)|^2  =  |P - c|^2 + 2 d (c - P).u + d^2 ,
    |P - (c - d u)|^2  =  |P - c|^2 - 2 d (c - P).u + d^2 ,
  =>  |P - (c + d u)|^2 - |P - (c - d u)|^2  =  4 d (c - P).u .             (*)
```

So the two roots differ by a term of **one sign** determined by the single scalar `(c - P).u`,
whose zero set is the same for both roots. Equivalently, in the lead's form
`|P - dn|^2 - R^2 = 2d(cos a - P.n)` (with `n` the normal and `a` the angle of `c`), the sign
and zero set are root-independent. That is exactly what makes C464's replacement
arc-preserving; the arcs of the two roots coincide as sets and the boundary-distance defect
has the same sign at both.

**Strictness is inherited with no smallness hypothesis.** `(*)` gives the sign for each root;
for strictness, `c' -> |P - c'|` is `1`-Lipschitz, so `|P - c'| <= |P - c| + d`; with the
pre-replacement nearest distance `<= r < R` and any `d < R - r`, every boundary point remains
strictly covered. The displacement `d` may be **large** (the inner root can move far); the only
requirement is `d < R - r`, so no small-perturbation or generic-perturbation hypothesis is used.

Full disk coverage after the replacement is C464's content (it holds for any radius, not only
the sharp one), so nothing else is needed here. Strict interiority of the two hubs is C451, and
`R` can be chosen arbitrarily close to `r` with `R < 0.38`, so the hubs stay interior.
**The claim is correct as stated.**

## 2. Sector height `> 0` — correct

The chord outward normal `n` and `k = cos(w_i/2)` give
`height = k - c_i.n >= sqrt(1-R^2) - |c_i| >= 0` since `w_i/2 >= asin R` and
`|c_i| <= sqrt(1-R^2)` after the inward-root replacement. Equality forces the whole chain
(`w_i = 2 asin R`, `c_i = sqrt(1-R^2) n`), i.e. both chord endpoints at distance exactly `R`
from `c_i`. But `P_i` lies in the nearest cell of `c_i` and boundary coverage is strict after
the replacement, so the nearest distance at `P_i` is `< R`. Contradiction; hence
`height > 0`. **Correct.** (Equivalently: strict boundary coverage is exactly what rules out
the degenerate zero-height sector.)

## 3. Positivity of the other triangles — correct

* Site faces: three distinct sites on one circle (radius `rho <= R`) are non-collinear, so the
  triangle is positive even when two incident Voronoi vertices coincide (zero-length primal
  diagonal). **Correct.**
* Switch triangle `(c_i, c_j, P_i)`: `P_i` is equidistant from `c_i, c_j` (i.e. it lies **on**
  their perpendicular bisector — correct as the draft says), and any point equidistant from two
  points and collinear with them is exactly their midpoint `m`; but
  `|m| <= (|c_i| + |c_j|)/2 < 1` while `|P_i| = 1`. So the triangle is positive.
  **Correct as the draft states it.** My earlier "not on their perpendicular bisector" sentence
  was wrong and is withdrawn; use the midpoint argument.
* Widths positive and `< pi` from the 9-arc ledger. **Correct.**

## 4. Consequence for the infimum — correct

`C835`: every positive assignment in `S` yields a genuine cover with allowance `R`, so
`r_D(11) <= inf_S R`. Conversely, a genuine cover at radius `r < 0.38` yields (by §1–§3)
positive assignments with allowances `R` arbitrarily close to `r`, so `inf_S R <= r`, and
taking the infimum gives `r_D(11) = inf_S R`. Hence no separate singular branch is needed for
lower bounds on the infimum. **Correct.**

## 5. Withdrawals (my earlier "corrections" to the lead — retracted)

Three items I raised in the previous message are **withdrawn**; the lead's proofs stand
unchanged.

1. **Euler/edge count.** `E = 48` is exact, enumerated. Hub degrees `6 + 7 = 13` counts the
   hub-hub edge `AB` **twice**, so the ring-hub edges number `11`, not `13`; internal edges
   `9 + 11 + 1 + 18 = 39`, boundary `9`, total `48`, and `20 - 48 + 29 = 1` as the lead wrote.
   My "38" was an arithmetic error of mine. Withdrawn.
2. **Strict sign / small displacement.** The multiplicative form `2d` with `d > 0` needs no
   smallness: the two roots share the boundary arcs and the sign of the defect, and `1`-Lipschitz
   continuity in the centre gives strictness for any `d < R - r` (I now say this in §1). My
   "with one step to spell out" is withdrawn as a correction; the lead's proof is unchanged.
3. **C836 circle ratios.** The `8` circle-ratio constraints of `C836` are **intrinsic** triangle
   ratios, not the `C816` cycle identities (those concern radii reconstructed on the unit
   circle). My attempt to drop the clause was based on conflating the two objects. Withdrawn;
   the clause stays.

No new exploration is pursued. My remaining remarks in §1–§4 are local checks only and are not
independent certification of the lead's interfaces.

## 6. Scope notes (as the lead states them, unchanged)

* The infimum need not be attained in `S`; saturation of the local radii is not claimed.
* The argument transfers lower bounds from `S` to the original problem; it does not produce a
  bound by itself, and finite grids/local KKT still do not bound `S` globally.
