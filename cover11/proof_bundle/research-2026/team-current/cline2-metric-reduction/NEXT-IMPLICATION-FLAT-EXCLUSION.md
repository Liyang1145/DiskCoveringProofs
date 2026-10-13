# Next implication: from the flat-patch (alpha2 = pi) exclusion to global n11 sharpness

Own directory, own scope. Sources read: `lead/HIGH-BEARING-FLAT-PATCH-EXCLUSION.md`,
`lead/HUB-ALL-BEARING-BOUNDARY-REDUCTION.md`, `lead/assemble_highbearing_boundary.py` and the
three certificates, and claims C835-C849. Report-level; no claim registered; no new grid used as
proof (the two calibration runs below are checks of an elementary scaling law).

## 0. The chain, and what the flat exclusion actually buys

| step | content | status |
|---|---|---|
| C835 | positive q0k4 flat metric (20 v, 29 f, angle sums 2pi at 11 sites) develops injectively; local radii <= R gives a genuine cover | proved |
| C836 | positive branch: 9 circle closures solve for the 9 widths, `R` their common value; intrinsic scaling forces `max 20 radii = 1` | proved |
| C837 | global n11 infimum = inf of recovered `R` over the **positive** q0k4 model with `R < .38` | proved |
| C838/C839 | 6 of 8 circle equalities suffice; 42-angle model with fitness `R_shape = M q0/ell0` | proved |
| C840-C851 | quantitative local domain incl. `alpha2 <= pi - 1e-8`, pair separation, tangency bounds | proved |
| C848/C849 | `alpha2 = pi`: explicit `H` fiber; fixed `(r,b1,b2,A)` makes the seven-factor objective separable in `(w1,w3,H)` | proved |
| C861/C863/C869 + stationary cert | `alpha2 = pi`, **high bearing** `bj >= 1`: maximum lies on one of three circle boundaries, each bounded | proved (restricted) |
| assembly | constant + 22 factor bounds + 3 boundary uppers `= 3.1414960605580249... < pi`, min margin `9.659e-05` (stationary-face component) | proved (restricted) |

The assembly margin is `min` over components: stationary face `9.659e-05`, ridge `1.448e-04`,
norm boundary `3.894e-03`. Coefficients: frozen hash `5671967c5a3df341...`, constant `-23.4412`
(`pi*(sum z[0:9] + 2 sum z[9:11] - sum z[112:])`), 22-factor sum `-1.5242`.

## 1. Answer to the asked question: what still has to be excluded

The positive model of C835/C836 has an **open** domain, so `alpha2 = pi` is a boundary stratum.
Excluding it leaves exactly these classes:

1. **`alpha2 = pi`, low bearing** (`min(b1,b2) < 1`) — **open.** The three boundary certificates
   assume `bj >= 1`; `HUB-ALL-BEARING-BOUNDARY-REDUCTION.md` states that for `b1+b2 < pi/2` the
   face ridge-side inequality changes sign and at `pi/2` the two face circles coincide, so these
   cases need explicit coverage. C871 supplies the all-bearing **hub-boundary reduction** (max on
   one of the three circles for all `r in [.375,.38]`) but **not** the bound on the low-bearing
   circle arcs.
2. **`alpha2 < pi`, all bearings** — **open**, and this is the generic stratum. The flat exclusion
   says nothing about it: no certificate in the record is expressed on the non-degenerate sector.
3. Other flat sectors (`alpha0`, `alpha4 = pi`) — presumably relabelling of the same machinery;
   not analysed here.

So: excluding the whole flat high-bearing patch yields the sharp optimum for **no** class. The
two missing classes are (1) and (2), and (2) contains (1) as the `alpha2 -> pi` limit.

## 2. Deformation/compactness: the collar extension, with the correct scaling law

I set out to extend the exclusion to `alpha2 in [pi - eps, pi]`. The first thing the attempt
produces is a **correction to my own preliminary picture**, and it is quantitative and useful:

**The flat limit is approached through the switch width, not by moving the site.**
With `P1, P2` the two switch points of the middle sector and `c2` the site at distance exactly
`r` from both, the triangle `(c2,P1,P2)` degenerates exactly when the chord half-length
`sin(w2/2)` reaches `r`, i.e. at `w2* = 2 asin r`. Writing `2 sin(w2/2) = r - delta` (so
`w2 = w2* - d`), one gets the elementary tangent-chord identities

```
    eps := pi - alpha2 = 2 arcsin delta/(2 sin(w2/2)) ,      h = dist(c2, chord) = sqrt(delta (2r - delta)) .
```

Both vanish **linearly in `delta`** (and only quadratically in `d = w2* - w2`). Calibration
(`r17_2_flat_limit.py`, `r = 0.38`):

```
    delta       h           eps         h/eps
   1e-2     5.913637e-02  3.125142e-01  0.189228
   1e-3     1.874345e-02  9.868979e-02  0.189923
   1e-4     5.928550e-03  3.120416e-02  0.189992
   1e-5     1.874815e-03  9.867487e-03  0.189999
   1e-6     5.928699e-04  3.120369e-03  0.190000
```

`h/eps` converges to a constant (`~0.190` at `r = 0.38`; the limit is
`c_1 = lim h/eps = 1/(2 sqrt(2r)) * ... `, bounded and positive on `r in [3/8, 19/50]`), which is
exactly the uniform linear rate the deformation argument needs:

```
    h(eps) = c_1(r,b) eps + O(eps^2) ,     0 < c_1^- <= c_1 <= c_1^+ < infinity on the class.
```

**Consequence for the geometry of the collar.** C842 already forces `alpha2 <= pi - 1e-8`, i.e.
`eps >= 1e-8`, i.e. `delta >= ~5.93e-9` at `r = 0.38`. The near-flat stratum is therefore the
family

```
    Q_0^+ := { 0 < delta <= delta_max(r) ,  w2 = w2*(r) - d(delta) } ,   h in [c_1^- 1e-8 , h_max] ,
```

a genuine one-parameter collar with `h` bounded **below** away from `0` once `alpha2 <= pi - 1e-8`
is imposed. This is the key structural fact that was missing: the near-flat stratum is *not* a
degenerating family under the C842 cut, so the frozen-dual functional can be evaluated on it.

**The extension statement that follows** (with the caveat in §3):

> **(EXT, conditional)** Let `F` be the assembled frozen-dual functional (constant + 22 factors +
> the three boundary uppers) and `L_F` a Lipschitz constant for `F` in the local shape
> parameters on the union of the three certificate domains. Then every configuration of the
> near-flat high-bearing class with `pi - alpha2 <= eps` satisfies
> `F <= pi - delta_asm + L_F c_1^+ eps`; hence the class is infeasible whenever
> `eps < delta_asm / (L_F c_1^+) =: eps*`, with `delta_asm = 9.659e-05`.

## 3. Why (EXT) is not yet a proof, and what the real obstruction is

Three honest caveats, in decreasing order of severity:

**(a) The certificates are not parametrized by `eps`.** The three certificates bound the maximum
over their own domains (`domain` fields: stationary face `r in [.379,.37999]`, `b1,b2 in
[1,1.1864]`, `delta in [-1.1864,1.1864]`; norm boundary `r in [.375,.38]`, `b1,b2 in
[1,1.1864]`; ridge `r in [.379,.37999]`, `b1 in [1,1.1864]`, `b2 in [g,0.7796]`). They are
interval bounds of `F` at stationary/boundary points, **not** of the map
`eps -> sup F`. So `L_F` in (EXT) is a Lipschitz constant for `F` as a function of the shape
parameters **with the relaxation held fixed**; producing it requires differentiating the same
expressions with respect to `(w2, A, alpha2)` and enclosing the derivatives on the union domain.
That is a mechanical (AD) obligation, not a conceptual one, and it is the first thing to do.

**(b) `Q_0^+` is not inside any single certificate box.** The certificates' `b`-ranges start at
`1`; the collar includes `b1` or `b2` down to `acos(r)/2 ~ 0.59`. So (EXT) as stated only covers
the **high-bearing** part of the collar. The low-bearing part of the collar is class (1) again,
and it needs its own boundary certificate (the sign reversal at `b1+b2 = pi/2` noted in
`HUB-ALL-BEARING-BOUNDARY-REDUCTION.md`). Nothing about the flat exclusion removes this.

**(c) Even a maximal collar leaves the interior.** `eps*` is a finite number
(`delta_asm/(L_F c_1^+)`, order `10^-4/L_F`), so (EXT) covers a collar, not `Q_+`. Extending
beyond the collar is not a compactness argument: `sup_{Q_+} F` over the open interior is a
different computation, and the four structural premises (high/low bearing, hub-lens shape,
`A` vs `b1+b2`) each define a separate piece whose certificate does not follow from the flat one.
This is where "flat exclusion -> sharp optimum" actually fails, and the failure is not a gap in
rigour but a missing object (next section).

## 4. The minimum missing exact interface

**(I-min, recommended)** An explicit parametric description of the seven-factor patch at
`alpha2 < pi` together with a fiber-supremum identity of the same shape as C849:

> For every allowed `(r, b1, b2, A, alpha2)` with `alpha2 < pi`, and fixed `(r,b1,b2,A,alpha2)`,
> the local patch necessary relaxation's objective is a constant plus finitely many **univariate**
> functions with explicit intervals (the C849 separability survives the removal of the
> `alpha2 = pi` degeneracy), with `alpha2` entering through the sector height `h` of §2 (or
> equivalently through `delta` and `w2`).

Why this is the minimum and not something weaker:

* It is the only object that closes classes (1) and (2) **simultaneously**: with it, the existing
  interval AD applies unchanged to a finite-dimensional parametrization and no new global dual is
  needed.
* It is exactly what the flat certificates are the `alpha2 -> pi` limit of, so producing it also
  *explains* the flat certificate as a boundary case rather than an isolated computation.
* It is metric, not combinatorial: at `alpha2 = pi` the sector triangle degenerates, and the
  C849 derivation (chord-width identity + non-degenerate switch triangles) must be redone with
  `alpha2` free, where `h(alpha2)` of §2 is the new variable coupling `A`, `w2` and the two
  switch radii.

The stronger alternative — one frozen dual feasible and `< pi` on all of `Q_+` — would close
everything at once but is not what the record supports (three separate boundary certificates plus
a stationary reduction were needed), and I do not recommend pursuing it.

## 5. One executable structural next obligation (O1)

**O1 (own scope, AD-only, no grids as proof).** On the union of the three certificate domains,
compute by interval AD the two quantities

```
    L_F := sup over the union domain of |dF/d(local shape parameters)|
           (F = constant + 22 factor bounds + the three boundary uppers, shape parameters
            = (w2, A, alpha2) and the hub variables, with the relaxation held fixed), and
    c_1^+ := sup over r in [3/8,19/50] and legal w2 of  h/eps   (from §2; calibration gives
            ~0.190 at r = 0.38),
```

then report the resulting collar width `eps* = 9.659e-05 / (L_F c_1^+)`.

Acceptance: an interval enclosure of `L_F` and `c_1^+` with `eps* > 0`, which yields (EXT) for the
high-bearing collar. If `eps*` falls below the certificate's own box resolution, the follow-up is
to re-run `certify_stationary_face_bound.py` / `certify_patch_cancel_outer.py` on the
`eps`-enlarged boxes (a certificate re-run, not a new experiment).

**Explicitly not part of O1:** closing the low-bearing arcs (class 1) or the non-flat interior
(class 2) — those need (I-min), not a collar estimate.

## 6. Non-claims

No claim that the flat exclusion implies the sharp optimum, in whole or in part; no promotion of
C863/C869/C870 past `bj >= 1`; no new grid as proof; no claim that (EXT) is proved (it is stated
conditional on `L_F`, whose enclosure is exactly O1); no claim about `r*` beyond C249/C335.
