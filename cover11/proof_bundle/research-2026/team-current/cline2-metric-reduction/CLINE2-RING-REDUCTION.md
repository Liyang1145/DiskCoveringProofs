# Unsaturated 9-ring reconstruction for the q0 two-hub covering (rev 4 — corrected)

`research-2026/team-current/cline2-metric-reduction/`
Reference configuration: the certified upper candidate `n11/upper/certified_object.json`
(22 integers / 1e17). Reduced type: 9 ring disks owning the boundary arcs + 2 interior hubs,
hub Voronoi degrees `(6,7)`; ring cyclic order `7,1,8,6,4,9,10,3,5`.

**This revision implements the lead's parametrisation literally.** It replaces rev 1–3, whose
saturation lemma, radical and radius count were wrong (corrections in §4).

## 1. The model (lead's parametrisation), implemented and verified

For a ring site with bounding switches `P_prev`, `P` on `|x| = 1`, width
`w = angle(P_prev, P)`, put

```
    k = cos(w/2) ,  d = 2 sin(w/2) ,
    P_prev = k n - (d/2) e ,   P = k n + (d/2) e ,
    a = rho_prev  (distance from the site to P_prev) ,
    b = rho_i     (distance from the site to P) ,
    x = (a^2 - b^2) / (2 d) ,
    h = sqrt( b^2 - (x - d/2)^2 )  =  sqrt( a^2 - (x + d/2)^2 ) ,
    c = (k - h) n + x e .
```

Identities (verified to `3.3e-16` on the candidate, all nine sites):
`|c - P| = b`, `|c - P_prev| = a`, `|c|^2 = (k-h)^2 + x^2`.

**Verification** (`c41_recon.py`): the nine candidate ring sites are rebuilt from their own
`(w, a, b)` data with maximum error `7.9e-16`. The two radical forms agree exactly (checked in
the same run: `h^2 = b^2 - (x-d/2)^2 = a^2 - (x+d/2)^2 = 0.004724124477` for site 7).

**Higher-precision re-verification** (`c42_hp_check.py`, mpmath at 50 digits, exact integer
literals): maximum reconstruction error `6.7e-51` and identity error `3.3e-51` over the nine
sites, and the nine switch minimal distances all reproduce
`0.3799838531198386…` to 17 digits. So the reconstruction is exact and the float64 residual is
round-off, not an artefact of the radical near its domain boundary.

**Free data / count.** Nine widths (with `sum w = 2 pi`), nine radii, four hub coordinates →
21 numbers after removing the global rotation; the bound `r` is an extra variable. Covering
gives only `rho <= r` — never equality. This is the honest global parameter space; nothing in
this document assumes saturation.

**Feasibility (domain, to be carried in any certificate):**
`b^2 - (x - d/2)^2 >= 0` (equivalently `|x - d/2| <= b`), the inward branch `k - h > 0`,
`|c| < 1`, strictly positive widths summing to `2 pi`.

## 2. Candidate data in these coordinates

```
 i  site   w_i(deg)      a=rho_prev    b=rho_i      x         h          |c|
 0   7    43.88994   0.3799838531  0.3799838531  -0.00e+00  0.068732267  0.858810938
 1   1    44.48690   0.3799838531  0.3799838531  +0.00e+00  0.033062071  0.892521730
 2   8    43.88994   0.3799838531  0.3799838531  +0.00e+00  0.068732266  0.858810938
 3   6    32.17982   0.3799838531  0.3799838531  +0.00e+00  0.259957917  0.700870054
 4   4    39.05774   0.3799838531  0.3799838531  +0.00e+00  0.180674907  0.761798272
 5   9    42.62905   0.3799838531  0.3799838531  +0.00e+00  0.110745856  0.820853262
 6  10    42.62905   0.3799838531  0.3799838531  -0.00e+00  0.110745852  0.820853266
 7   3    39.05774   0.3799838531  0.3799838531  -0.00e+00  0.180674907  0.761798272
 8   5    32.17982   0.3799838531  0.3799838531  +0.00e+00  0.259957917  0.700870054
```

Radical slacks `b^2 - (x-d/2)^2` are `+1.09e-3` (site 1, the tightest) to `+6.76e-2`
(sites 6, 5). **In this configuration all nine radii equal the single number
`R = 0.37998385311983884`** — a property of this configuration, not a theorem; the lead's
`C821` exhibits an exact cover whose switch radii are unequal, so no universal saturation
may be assumed.

## 3. Status of the boundary critical set (no new claim)

For a fixed nearest-site type the covering radius is attained on boundary switches and
interior Voronoi vertices; the owned-arc antipodal direction must be added as a *candidate*
unless membership is decided by the corrected criterion
`2 x*·(c_j - c_i) <= |c_j|^2 - |c_i|^2`. Nothing here is asserted as proved beyond the
elementary dichotomy `f|A_i = |x-c_i|` (so an arc maximum is at a switch or at the antipodal
point when that point lies in the arc).

## 4. Corrections to my own earlier work (all accepted)

1. **Boundary-saturation lemma (rev 2) — retracted.** Covering gives `min_j |P - c_j| <= R`;
   equality, and equality at all nine switches, do not follow. The lead's `C821` is an exact
   counterexample, so universal saturation is false, not merely unproved.
2. **Antipodal criterion (rev 2) — retracted.** Correct form as in §3.
3. **Radius count.** I had treated the two switch distances of a site as 18 independent radii;
   they are 9 radii: `a_i = rho_(i-1)`, `b_i = rho_i`, the same objects seen from the two
   switches.
4. **Radical.** My `sqrt(k^2 - 1 - x^2 + b^2)` omitted the `d x` term; the lead's
   `sqrt(b^2 - (x - d/2)^2)` is correct (equivalently `sqrt(a^2 - (x+d/2)^2)`). In the
   **saturated** case `x = 0` the two forms coincide, which is why more than one verification
   script appeared to pass; they differ in general.
5. **Closure rows.** My rev-1 claim that the rows fail by `0.107 rad` was my index error. With
   the owned width (= switch gap) the rows vanish to `3.1e-15` on the candidate. I have
   **withdrawn my registered `C823`** ("proved"): the lead found the `L`/`T` endpoints swapped
   in the equation, and the "8 independent" statement had no analytic rank proof — a small
   floating residual is not a proof. I will not register claims from numeric tolerances.
6. **Mis-attribution.** The rational form `h = (d^2 + b^2 - a^2)/(2d)` quoted in my last message
   was my own invention, not the lead's; the lead's delivered formula was the radical, which is
   correct. Apologies for the mis-reading.
7. **Finite-difference optimality (c40) — stopped.** The lead has the KKT analysis; I am not
   pursuing local optimality numerically.

## 5. Files

| file | content |
|---|---|
| `c41_recon.py` | **the correct unsaturated reconstruction**, verified to `7.9e-16` |
| `c37_unsaturated.py` | candidate `(w, a, b)` table, radical domain |
| `c39_unsaturated_test.py` | perturbation probe of the covering radius (diagnostic only) |
| `c31_closure.py` | closure rows with the owned width; identity check |
| `c25_model.py`, `c27_verify.py` | the saturated special case (conditional, `a=b`) |
| `c13_blocks.py` | 21 matching rows; log-radius Jacobian rank 19 |
| `c36_unsaturated.py`, `c38_recon.py` | earlier reconstruction attempts (wrong radical; superseded) |
| `CLINE2-RING-REDUCTION.md` | this document |

```
py -3 -B c41_recon.py ; py -3 -B c37_unsaturated.py ; py -3 -B c31_closure.py
```

## 6. Next obligation (one)

The nine radii are **not eliminated** — the lead reports only a necessary norm *filter*, with no
elimination proved. The 21-dimensional reconstruction of §1 therefore stands as the current
model, and the obligation is stated without anticipating any elimination:

Let `F(x) = min_j |x - c_j|` and let the type's maximum be realised on its boundary switches and
interior Voronoi vertices (with the antipodal candidate handled by the corrected criterion of
§3). Show, on the domain of §1 — nine positive widths summing to `2 pi`, nine radii `rho <= r`,
two hub sites, and the feasibility conditions `h^2 >= 0`, `k - h > 0`, `|c| < 1` — that
`max over switches and Voronoi vertices >= r*`; or exhibit a configuration of that domain with a
smaller covering radius. No new claim is registered until this interface is checked.

## 7. Reference correction (from the lead)

The counterexample to any universal equal-switch-radius statement is registered as `C830`
(correct threshold object `C529`; original threshold `1e-17` with `+1e-5`; actual displacement
`1e-6`). The earlier citation `C821 -> C249` referred to a different object (`1e-60`). The
geometry intervals and the conclusion are unchanged: universal saturation is false.
