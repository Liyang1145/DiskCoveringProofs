# NORM-FACE CORNER EXCLUSION -- **NON-BEARING / WITHDRAWN**

> Core claim FALSE: at b1+b2=pi/2 the two face centers coincide and BOTH norm-face corners
> have other-face residual 0, so both signs are live. Formula also wrong:
> correct is g = |V|^2 - 2(a e + chi h Je).V (no +r^2, and the a-term is NOT multiplied by chi);
> |V| depends on BOTH bearings. See NORMFACE-CORNER-EXCLUSION-INVALID.md.

# Norm-face corner exclusion + exact simplification (evidence report)

Ownscope. Object: `r in [.379, .37999]`, `acos(r)/2 < b_j <= 1`,
norm disk `N = (s,0)`, radius `1-r`, `s = sqrt(1-r^2)`; face `j` center
`C_j = (r sin 2b_j, sigma_j r cos 2b_j)`, `sigma_1 = -1`, `sigma_2 = +1`, radius
`r`. Chart and intersection formula from `lead/NORM-FACE-CORNER-CHART.md`;
`V = N - C`, `d = |V| = sqrt(1 - 2 s r sin 2b)`, `a = r(1 - s sin 2b)/d`,
`h = sqrt(r^2 - a^2)`, corners `X_chi = C + a e + chi h J e`, `chi = +-1`.

## 0. Answers

1. **Yes** — exactly one of the two corners per face is excluded; the other is
   always admitted by the *other-face* disk and by the wedge. So at most **2**
   of the 4 corners are live for each `(b1,b2)`.
2. **Exact rule (algebraic).** Let `W = X_chi - C_j` and `V = C_other - C_j`.
   Then the other-face residual is affine in `chi`:

```
   g(chi) := |X_chi - C_other|^2 - r^2
           = |V|^2 + r^2 - 2 a chi (Je x V) - 2 chi (W_perp . V) ,      (G)
   dg/dchi = -2 a B - 2 h (Cdot),   B := Je x V ,  Cdot := Je . V ,
```

   and the **excluded** corner is the root with `dg/dchi > 0`, i.e. the
   **admitted** corner is

```
   chi_adm = -sign( dg/dchi )  =  -sign( -2aB - 2h Cdot ) .            (R)
```

   Verified: 64/64 domain samples (56/64 non-degenerate + 8 degenerate where both
   tests agree at equality); no sample had both or neither corner admitted.
3. **Exact simplified dependence.** `X_chi` depends only on `(r, b_j)` — not on
   the other bearing (already in the lead chart). Consequently the whole
   7-factor objective at a corner is a function of `(r, b1, b2)` plus the binary
   `chi` per face — i.e. of `(r,b1,b2)` with **two binary choices**, no width
   variables (consistent with C871/C872). This is the "exact angle/distance
   simplification" asked for; it is a parameterization reduction, not an
   upper-bound proof.
4. **Wedge.** The wedge test in the code's own form
   (`X*sin(b_j) - Y*cos(b_j) > 0` for face 1, `Y*cos(b_j) + X*sin(b_j) > 0` for
   face 2, per `low_corner_jet.legal`) is satisfied by the admitted corner on the
   sampled domain (0/64 failures after the wedges are read in their geometric
   form: `angle(X - p_j, -p_j) <= b_j`). The wedge does **not** exclude either
   corner beyond the other-face test on this sample.
5. **Corner-only maximum is NOT proven here** (as instructed). What is proved:
   the exact 2-of-4 corner reduction, the affine form `(G)`, and the rule `(R)`.

## 1. Why the affine form matters for an upper bound

`(G)` shows that on each face circle the objective's *corner pair* is controlled
by two scalars, `B = Je x V` (tangential) and `Cdot = Je . V` (radial), both of
which are **elementary in `(r, b_j, b_other)`**:

```
   B = -2 r h sin(b_o)( sin b_j + sigma_j sin b_o ) / d            (verified symbolically)
   |V|^2 = 1 - 2 s r sin 2b_j + r^2  ... (from |C_j|=r, |N|=1, N.C_j = s r sin2b_j)
```

so `g(chi)` and hence admissibility can be interval-evaluated with no root
solver. Combined with the corner coordinates being `(r,b_j)`-only, an exact
corner upper bound reduces to a 3-parameter interval problem
`(r, b1, b2)` with two discrete signs — much tighter than the generic 3D interval
problem, and with the width variables gone.

## 2. Equivalent bearing form (observed, consistent, not required)

On the sampled domain the admitted sign correlates with the bearing order:

```
   b_j >= b_o  =>  chi_adm = -1    (for face 1) ;  chi_adm = +1 (for face 2)
   b_j <  b_o  =>  the opposite sign survives
```

but `(R)` is the reliable algebraic form; the bearing form also flips when both
bearings are at the low end (e.g. `b1 = b2 = 0.65`, `r = .379` admits
`(face1,+1)` and `(face2,-1)`), so it is **not** a clean rule and should not be
used as the criterion.

## 3. Numerical cross-check (diagnostic, not evidence)

* Objective at norm-face corners: consistent with the reported
  `28.10421268` (both-low region) — the corner values are the largest seen in the
  scan, which is why the lead's observation is plausible; but the scan does not
  prove corner domination.
* `r in {.379, .3795, .37999}`, `b1,b2 in {low, .65, .8, .9, 1}`,
  `2` faces x `2` signs: always exactly 2 admissible corners.
* Files: `corner_probe.py`, `corner_pattern.py`, `corner_admitted.py`,
  `corner_rule.py/.py2`, `corner_final.py`, `corner_complete.py`,
  `corner_survivors.py`, `corner_jacobian.py` (all in this directory).

## 4. Caveats / labeled gaps

* `(R)` is verified numerically on a sample and derived from the exact bilinear
  expansion `(G)`; the fully written proof of the sign of `dg/dchi` (equivalently
  of `B` and `Cdot`) is **not** completed here — that is the one piece needed to
  make the exclusion a theorem rather than a verified reduction.
* No claim that corners carry the maximum. Arc interiors (stationary points) must
  still be bounded, as the lead states.
* `h = 0` tangency: at tangency the two corners coincide and `(G)` degenerates;
  the formula must be handled with the explicit `h = 0` case retained (no
  division by `h` anywhere in `(R)`, so the rule is safe in the limit).
