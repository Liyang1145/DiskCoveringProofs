# Withdrawal R17 + corrected flat-limit geometry (own scope)

Supersedes the deformation section of `NEXT-IMPLICATION-FLAT-EXCLUSION.md` (§2, §3(c), §5's
`c_1^+`). The lead's corrections are confirmed; the correct geometry turned out to be a mix of
both readings, and the outcome changes the collar estimate by an order of the margin.

## 1. Withdrawn (my Round-17 deformation claims)

| # | claim | status / reason |
|---|---|---|
| D-w1 | the flat limit of the sector width is `w = 2 asin r` | **WITHDRAWN.** At exact flatness (`alpha2 = pi`) the site is at the chord midpoint and the chord is `|P1P2| = r`, so the site's arc width tends to `2 asin(r/2)`, as the lead said. |
| D-w2 | `eps := pi - alpha2 = 2 arcsin(delta/(2 sin(w/2)))` | **WITHDRAWN.** No such identity; it was extrapolated, not derived. |
| D-w3 | `h = sqrt(delta(2r - delta))` | **WITHDRAWN.** Wrong by the factor `sqrt(2)` in the exponent sense and wrong in structure: the exact closed form (below) is `h = r sin(eps/2)`. |
| D-w4 | "`h/eps -> const`, hence a linear collar `h = c_1 eps + O(eps^2)`" | **WITHDRAWN.** In the chord-deficit parametrisation `h/eps` diverges as `eps -> 0`; only in the site-width-deficit parametrisation is `h/eps` bounded. The reported constant `0.190` is real but belongs to a different parameter. |
| D-w5 | the numerical scan `r17_2_flat_limit.py` as evidence for a linear collar | **VOID.** That scan forced `|site - Pj| = r` for **both** endpoints with the chord endpoints held fixed; in the physical family only the two switch radii equal `r`, so the scan measured a non-physical one-parameter subfamily (`h/eps -> 0.190` is the chord-suppression slope there). It is not evidence for the physical family. |
| D-w6 | "C842 bounds `alpha2 <= pi - 1e-8`" | **WITHDRAWN.** `claim_get C842`: status `proved-interval`, scope "two **endpoint** sector boundary branches", statement "the sectors at the two common-hub ring endpoints 0 and 4 cannot have `alpha = pi`", and its own scope line says "other 7 sector degeneracies not excluded". C842 constrains `alpha_0`, `alpha_4`; it says nothing about `alpha_2`. My epsilon assertion was invented. |
| D-w7 | the conditional collar `eps* = 9.659e-05/(L_F c_1^+)` | **WITHDRAWN as stated** (it used D-w4 and D-w6). A corrected version is below; the change is that the collar width in `delta` is `O(margin^2)`, not `O(margin)`. |

`DEAD.md` updated with entry `R17-E2`.

## 2. Correct exact flat-limit geometry

Site `M` at the origin, switches `P_pm = (u, ±v)`, unit-circle centre `C = (a, 0)`:

```
    u^2 + v^2 = r^2          (switch radii = r)
    (u - a)^2 + v^2 = 1      (switches on the unit circle)
    alpha2 = angle at M,  h = dist(M, span(P+P-)) = u
    2 sin(w/2) = |P+P-| = 2v  (site's arc width)
```

The two constraints give `a = u - sqrt(1 - v^2)`, and the law of cosines in the isosceles triangle
`M P+ P-` gives the **exact** relations

```
    v = r cos(eps/2) ,     u = r sin(eps/2) ,     eps := pi - alpha2 ,
    h = r sin(eps/2)  =  r eps/2 + O(eps^3) ,
    w = 2 asin v = 2 asin r - r eps^2 /(4 sqrt(1 - r^2)) + O(eps^4) ,
    delta_site := w_flat - w = r eps^2 /(4 sqrt(1-r^2)) + O(eps^4)        (quadratic in eps)
    delta_chord := 2r - 2v = r eps^2/4 + O(eps^4)                          (quadratic in eps)
```

Numerical confirmation (`r17_6_closed_form.py`, `r = 0.38`):

```
    eps        h            delta_site     h/eps      delta_site/eps^2   h/sqrt(delta_site)
  3.0e-01   5.678649e-02    9.217367e-03   0.189288      0.102415           0.591482
  3.0e-02   5.699786e-03    9.243117e-05   0.189993      0.102701           0.592856
  3.0e-03   5.699998e-04    9.243376e-07   0.190000      0.102704           0.592870
  3.0e-04   5.700000e-05    9.243378e-09   0.190000      0.102704           0.592870
```

with the closed forms matching to 12 digits (`h = r eps/2`, `delta = r eps^2/(4 s)`,
`r eps^2/(4s) = 1.027042e-09` vs exact `1.027042007e-09` at `eps = 1e-4`).

**So the sharp statement is:**
```
    h ~ eps  ~ sqrt(delta)        (NOT linear in delta)
    h/delta ~ eps^{-1} -> infinity
```
Both readings meet here: with the lead's chord-deficit parametrisation `2 sin(w/2) = r - delta`,
`delta` is quadratic in `eps`, hence `eps ~ sqrt(delta)` and indeed `h ~ sqrt(delta)`; the
`h ~ delta` behaviour I reported is false, and the constant `0.19` is the coefficient of `h/eps`
(an `O(1)` ratio in the *other* variable), not a linear collar coefficient.

## 3. Corrected consequence for any collar/Lipschitz argument

A Lipschitz bound `|F - F_flat| <= L_F h` together with a flat-class margin `delta_asm = 9.659e-05`
gives a collar in the **height**:

```
    h <= delta_asm / L_F        =>       eps <= 2 delta_asm/(r L_F)      (h = r eps/2)
    and in terms of the width deficit:
        delta_site <= r (2 delta_asm/(r L_F))^2 / (4 s)  =  O(delta_asm^2 / L_F^2)
```

i.e. the collar is of width `O(margin)` in `eps` and `O(margin^2)` in the width deficit. The
margin is `9.659e-05`, so `delta_site ~ 10^-9` — the collar is much thinner in the width variable
than my withdrawn estimate, and this is the honest quantitative cost of the `sqrt` degeneracy.

## 4. The lead's parameter-projection condition, made precise

Any such collar claim must come with a **projection `Pi`** from the near-flat family to the flat
class that (i) preserves the local-patch domain, (ii) is Lipschitz with a *uniform* constant, and
(iii) is compatible with the necessary conditions (the same inequality set must hold at
`Pi(config)`). The `sqrt` law above shows the naive projection "keep `(r, b1, b2, A)` and shrink
`alpha2`" does **not** have a uniform Lipschitz constant in the width variables: the map
`delta -> h` is `delta -> sqrt(delta)`, whose derivative blows up at `delta = 0`. The correct
projection is by the **height** `h` (or by `eps`), for which the map is differentiable with
bounded derivative on the closed collar `0 <= h <= h_max`:

```
    Pi: (r, b1, b2, A, h)  ->  (r, b1, b2, A, h = 0)      (flat class)
```

being careful that the flat class's own certificates are stated at `alpha2 = pi` exactly. **No
Lipschitz collar claim is made here.** Without a verified `Pi`, the frozen-dual bound does not
transfer, which is exactly the lead's condition.

## 5. What survives from Round 17 (still bearing)

* The chain table (§0 of `NEXT-IMPLICATION-FLAT-EXCLUSION.md`) — unchanged and correct.
* **The structural gap statement**: the flat class is a *boundary stratum of an open positive
  domain*, so excluding it closes no class; the missing classes are (1) `alpha2 = pi` with
  `min(b1,b2) < 1` and (2) all `alpha2 < pi`, with the four structural premises each needing a
  separate certificate (the face ridge-side sign reverses at `b1 + b2 = pi/2`).
* **The minimum missing interface** (I-min): an explicit parametric description of the
  seven-factor patch at `alpha2 < pi` with a C849-shaped fiber-supremum identity, `alpha2`
  entering through the height `h` of §2 — now with the correct relation `h = r sin(eps/2)`.
* The margin accounting: `min` assembly margin `9.659e-05` (stationary face), `1.448e-04`
  (ridge), `3.894e-03` (norm); constant `-23.4412`; 22-factor sum `-1.5242`; hash
  `5671967c5a3df341...`.

## 6. Status

Deformation formulas and the C842 epsilon assertion: **withdrawn / non-bearing** (D-w1..D-w7).
No collar claim. No new numeric claim used as proof. The non-flat metric representation remains
the real gap, and the parameter projection `Pi` of §4 is a necessary component of any attempt to
close it by deformation.
