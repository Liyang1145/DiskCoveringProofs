# ω-fiber explicit interval -- **INVALID / DO NOT CITE** (see OMEGA-FIBER-AUDIT-INVALID.md)

> This file is superseded. It contains reversed B-direction inequalities, a dropped
> upper endpoint, a wrong sign in the alpha=pi,d=0 branch, an over-sharp norm bound and
> an unsupported |d| bound. Kept only as history. The lead SECTOR-SCALE-FIBER.md proof
> stands independently.

# ω-fiber: explicit interval (audit of the lead's reduction, corrected)

Own directory. Notation: `omega := w/2`, `u = s e^d`, `v = s e^{-d}`,
`s = sqrt(uv)`, `A := sin alpha`, `c := cos alpha`, `E := e^{2|d|}`,
`Q := 2(cosh 2d - c)`, `K := R0 sqrt(Q)/2` (so `sin omega = K s`),
`tmin := 75/76 <= rho := r/R0 <= 1`, `R0 = 19/50`.

## 0. Verdict

The lead's reduction is **correct and complete in its three equivalences**; the
fiber is one-dimensional in `omega`. One correction to my own first draft of
this audit: the endpoint-max upper bound and the covering upper bound are
**independent** (my "equivalent" claim was wrong; see §3), exactly as the lead
stated. Below is the merged explicit interval.

## 1. The three equivalences (proved; verified numerically)

```
  (L)   sin(alpha - omega) >= rho^2 sin(omega)
        <=>  sin(omega) sin(alpha - omega) >= K^2 rho^2
        <=>  cos(2 omega - alpha) >= cos alpha + 2 K^2 rho^2   =: B(rho)      (ω1)
        [identity sin omega sin(alpha-omega) = (cos(2omega-alpha) - cos alpha)/2]

  (C844') sin(alpha - omega) >= E sin(omega)
        <=>  omega <= omega_E(alpha,d) := atan2( A , E + c )                  (ω2)
        [valid when E + c > 0; equality case E + c = 0 handled in §4]

  (cov)  s e^{|d|} <= 1   <=>   sin omega <= K e^{-|d|}
        <=>  omega <= omega_cov(alpha,d) := asin( K e^{-|d|} )                (ω3)
```

All three are exact; `(ω1)` and `(ω2)` verified to 30 digits, `(ω3)` immediate.

## 2. The lower end: `(ω1)` gives an interval for `omega`, conditionally

`B(rho) = c + 2K^2 rho^2`.

```
  B in [-1,1]:  theta := acos(B) exists, and (ω1) is
                cos(2omega - alpha) >= cos B  <=>  |2 omega - alpha| <= theta
                <=>  (alpha - theta)/2 <= omega <= (alpha + theta)/2 .
  B < -1:       empty (no omega satisfies (ω1)).
  B > 1:        (ω1) holds for all omega (no lower bound from L).
```

So the L-constraint contributes the lower end `omega_lo^L := max{0,(alpha-theta)/2}`
(and an upper end `(alpha+theta)/2`, which is never binding because
`(alpha+theta)/2 <= alpha <= pi` but the true upper ends come from `(ω2)/(ω3)`;
see §3).

## 3. The upper end: two *independent* bounds, take the min

* `omega_E = atan2(A, E+c)`, with `sin omega_E = A/sqrt(A^2 + (E+c)^2)`
  (verified). As `alpha -> pi/2` this approaches `atan2(1, E)`, decreasing in `E`.
* `omega_cov = asin(K e^{-|d|})`, independent of which site is nearer;
  `K` grows with `|d|`, so this bound *tightens* with `|d|`.

Numerical comparison on a grid shows both regimes occur (tag = tighter bound):

```
  d=0.0 : C C C C C C C        (covering tighter for all tested alpha)
  d=0.1 : C C C C C C C
  d=0.3 : E C C C C C C        (endpoint-max tighter at small alpha)
  d=0.5 : E E C C C C C
```

so the effective upper end is

```
  omega_hi(alpha,d) := min{ omega_E(alpha,d) , omega_cov(alpha,d) }
```

except in the degenerate case of §4. (My earlier claim that `omega_E` is implied
by `omega_cov` is **retracted**: the two are independent, and either can be the
binding one.)

## 4. The `E + c = 0` branch: `alpha = pi`, `d = 0`

At `alpha = pi`, `c = -1`, `A = 0`, `E = e^{2|d|}`:

```
  (ω2):  sin(pi - omega) = sin omega >= E sin omega  <=>  (E-1) sin omega <= 0 .
```

* `d != 0` (`E > 1`): impossible for `sin omega > 0` — **no positive-width
  sector with `alpha = pi` and `d != 0`** (the lead's branch).
* `d = 0` (`E = 1`): `(ω2)` is `0 <= 0`, vacuous; `atan2(0,0)` is undefined and
  the bound is simply dropped. Then `(ω1)` reads
  `cos(2omega - pi) = -cos 2omega >= -1 + 2K^2 rho^2` with `K = R0` (since
  `Q = 2(1+1) = 4`), i.e. `2 sin^2 omega <= 2 R0^2 rho^2`, so
  `sin omega <= R0 rho`, i.e. `s <= rho`: the degenerate corner `s = rho`,
  `omega -> pi/2` is exactly the boundary. This is the corner the lead flagged
  (`alpha pi, x > tmin^2`), and it is retained by the `B(rho)` branch with
  `B = -1 + 2R0^2rho^2 in (-1,1)`.

## 5. Merged fiber (explicit)

```
  omega in [ omega_lo , omega_hi ] ,                                (Ω)
  omega_lo = max{ 0 , (alpha - theta)/2 , omega_qmin } ,   theta = acos( c + 2 K^2 rho^2 )
  omega_hi = min{ pi/2 , omega_cov , omega_E }              (drop omega_E when E+c <= 0)
  omega_cov = asin( K e^{-|d|} ) ,
  omega_E   = atan2( A , E + c )   (E + c > 0) ,
  s = sin(omega)/K in [ sin(omega_lo)/K , sin(omega_hi)/K ] ,
  and (ω1) also gives the redundant upper (alpha+theta)/2 >= omega_hi.
```

`omega_qmin`: the kernel's `qmin` filter is `q >= 4 sin^2(pi - 8 asin R0)/R0^2`
with `q = 4 s^2 (cosh 2d - cos alpha)`, and `w = 2 omega = 2 asin(K s)`; since
`w = 2 asin(sqrt(q)/2)`-type relations give `omega >= omega_qmin(d, alpha)` —
monotone (the filter is a *lower* bound on `s`, hence on `omega`). **Missing:**
the closed form of `omega_qmin` in `(d, alpha)` (elementary but not written here).

**Nonemptiness.** Numerically (18 `(d,alpha)` pairs, `rho = tmin`) the fiber
`(Ω)` was nonempty in every case tested; the criterion is
`omega_lo <= omega_hi`, i.e. in closed form
`max{ (alpha-theta)/2 , 0 } <= min{ asin(K e^{-|d|}) , atan2(A,E+c) }` plus the
`qmin` term. **Missing:** a proof that this holds on the whole admissible region
(and the identification of the empty region, if any).

## 6. Endpoint-distance lower bound (new input; verified) and fiber compactness

**Claim (lead).** For every genuine endpoint, `p, q >= 1 - sqrt(55)/8`, and in
`R0 = .38` units `u, v > 19/100`.

**Proof (independent check).** Let `P in bd D` be a boundary endpoint of a sector
whose centre is `c`, `t := |c|`. Since `|P| = 1`,
`1 = |P| <= |P - c| + |c| = p + t`, so `p >= 1 - t`. The inward condition gives
`t <= sqrt(1 - r^2)` and, since `r <= R0 = 19/50`,
`t <= sqrt(1 - (19/50)^2) = sqrt(2139)/50 = 0.924986486...`, which is
`< sqrt(55)/8 = 0.927024811...` (because `2139/2500 = 0.8556 < 55/64 = 0.859375`;
exact cross-multiplication: `2139*64 = 136896 < 137500 = 55*2500`). Hence

```
   p, q  >=  1 - sqrt(55)/8 = 0.072975189113042138...   (for EVERY genuine endpoint)
```

In `R0` units: `u, v >= (1 - sqrt(55)/8)/R0 = 0.192039971...  > 19/100`, the last
comparison exact via

```
   sqrt(55) < 8 ( 1 - (19/50)(19/100) ) = 8 * 0.9278 = 7.4224     (55 < 55.0917...)
```

so `1 - sqrt(55)/8 > 0.19 * R0` strictly. Comparison with the previous
`delta`-based endpoint lower bound (`~0.000026`): the new bound is
`0.072975/0.000026 ~ 2807` times larger.

**Immediate consequences for the fiber:**

* `s = sqrt(uv) > 19/100` and `u, v > 19/100` (both **uniform in** `(alpha, d)`).
* `omega = asin(K s)` with `K >= R0 sin(alpha/2)` (equality at `d = 0`), hence

```
   omega > asin( R0 sin(alpha/2) * (19/100) )   (d = 0 case; the general bound is the same
   with K >= R0 sin(alpha/2) on the admissible d-range),
```

  a strictly positive lower bound depending only on `alpha`; the minimum over
  `alpha in (0,pi]` is at the small-`alpha` end and tends to `0`, so the
  `alpha`-uniform statement is `omega > 0` and `omega >= asin(0.19 R0 sin(alpha/2))`
  for each `alpha`. In particular `omega = 0` is excluded for every genuine
  sector (consistent with `w > 0`).
* **Fiber compactness.** In `(s,d)` coordinates: `s in [s_min, s_max]` with
  `s_min = R0 e^{2|d|}/(2 rho)`, `s_max = e^{-|d|}` (both positive and, by
  `e^{3|d|} <= 2rho/R0`, bounding `|d| <= 0.5536`), and `omega in [omega_lo, pi/2]`
  with `omega_lo >= asin(0.19 R0 sin(alpha/2)) > 0`. Hence for each fixed
  `(alpha, rho)` the admissible set is a **closed bounded** subset of
  `(d, omega)`, and the fiber `(Ω)` is compact — no degenerate point at
  `omega = 0` or `s = 0` survives.

**Missing step.** The exact constant in the `omega` lower bound: it is
`asin(K s_min^u)` where `s_min^u = (1 - sqrt(55)/8)/R0` and `K = R0 kappa`; I have
not maximized `K` jointly with `s` over `d` (only the `d = 0` bound is displayed).

## 7. Corrections to my earlier draft `OMEGA-FIBER-AUDIT.md`

1. **Retracted:** "the endpoint-max condition is equivalent to the covering
   bound". They are independent; a grid comparison gives `omega_E < omega_cov`
   for `d = 0.3, alpha = 0.2` and `d = 0.5, alpha in {0.2,0.5}`, and
   `omega_cov < omega_E` elsewhere. The correct statement is the min in §5.
2. The claim `K^2(1+c^2) <= 1` as the crossing criterion was an artifact of the
   wrong equivalence; the crossing condition is the sign of
   `A/sqrt(A^2+(E+c)^2) - K e^{-|d|}`.
3. The `alpha = pi` treatment in §4 above is the correct one (vacuous only at
   `d = 0`; impossible for `d != 0`).

## 8. Verification files

`verify_U.py`, `verify_U2.py`, `verify_bounds.py` (grid comparisons, 30-digit
mpmath); `audit_omega.py` (the 160-point interval-membership scan against the
direct geometric constraints, 0 mismatches).
