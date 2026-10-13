# POLAR-PLUS-BRANCH-EXCLUSION -- **INVALID / DO NOT CITE**

> Superseded by lead/POLAR-PLUS-EXCLUSION-CORRECT.md. Errors here: (1) conflated the
> first coordinate H with v (the tcap and the radical are statements about v, not H);
> (2) used the wrong quadratic 2sv >= 2r(1-r^2) leading to the impossible bound
> 15/sqrt(55) = 2.0226 > 2 (the correct covering quadratic gives v >= 2r(1-r)/s ~ .505);
> (3) the tcap is immediate from the two face disks (t >= -r(1+cos2b1),
> t <= +r(1+cos2b2)), not a joint DN+wedge effect. The valid proof is in the lead file.

# POLAR plus-branch exclusion (corrected) — high-bearing region

**Supersedes `FAR-BRANCH-EXCLUSION.md`, which is INVALID** (it proved the
Cartesian half-space `v >= s`, not the polar `H+` root; the polar `+` root only
requires `v >= 2r(1-r)/s`, and the Taylor bound was the wrong truncation). Own
scope. No sampling is used as evidence; the numerics only re-check the rational
inequalities.

## 0. Result

```
THEOREM.  r in [3/8, 19/50], b1,b2 in [1, acos r], hub domain = three-disk
intersection (two face disks radius r, norm disk DN) ∩ wedge.  The polar "+"
(root = s cos(delta) + sqrt((1-r)^2 - s^2 sin^2(delta)), s = sqrt(1-r^2)) is
infeasible.  Hence only the "-" (near) branch of DN survives.
```

## 1. Exact geometry (from the frozen kernel chart)

Chart: `interval_cartesian_cancel.py` / `interval_hub_boundary.py`. Hub `X = (v,t)`;
disks `(cx, cy, rad)`:

```
  D1: ( r sin 2b1 , -r cos 2b1 , r )        D2: ( r sin 2b2 ,  r cos 2b2 , r )
  DN: ( s , 0 , 1 - r )                     s = sqrt(1 - r^2)   [physical hub norm]
  wedge:   -v tan b2  <=  t  <=  v tan b1
```

The norm constraint is the **physical** `|hub| <= 1-r` (disk of radius `1-r`
centred at `(s,0)`), not `sqrt(1-r^2)`; the polar data `(delta, H)` enter through
`(H - s)^2 + t^2 = (1-r)^2`, `t = H tan delta`, giving the two roots
`H± = s ± sqrt((1-r)^2 - s^2 sin^2 delta)` on DN.

## 2. The two necessary bounds

**(B1) tangential cap.** For a feasible hub (`(v,t)` in `D1 ∩ D2 ∩ DN ∩ wedge`);
on DN the extreme points in `t` are reached on the norm circle, and the observed
maximum matches `r(1+cos 2)`:

```
  |t|  <=  r (1 + cos 2)  =  0.221864202...        (analytic form; see §4)
  verified max over the domain: 0.221863858  (grid, 27 outer triples, gap 3.4e-7)
  outward rational form:  |t| <= 223/1000  <  .224       [covers the 3.4e-7 slack]
```

**(B2) covering lower bound on `v`.** The hub must cover a point of `bd D`, so
`|hub| >= 1-r`; combined with the DN quadratic
`v^2 - 2sv + t^2 <= 0`:

```
  v^2 + t^2 >= (1-r)^2 ,   v^2 + t^2 <= 2 s v
  =>  2 s v >= (1-r)^2 >= ...   (radical condition)
  =>  v  >=  2 r (1-r) / s .
```

**Correction of my own arithmetic:** `2r(1-r)/s` with `s = sqrt(1-r^2)` is
`0.509412848...` at `r = 19/50` and `0.505649897...` at `r = 3/8`; the value
`0.760` I printed earlier was the wrong quantity `2r(1-r)/(1-r) = 2r`. The lead's
`~0.504` is right.

## 3. The chain

On the DN circle, `(H-s)^2 = (1-r)^2 - t^2`, so `H = s - sqrt((1-r)^2 - t^2)` on
the near side; for the **far/plus root** the file's characterization is
`H+ >= 2r(1-r)/s` (§2, B2). Suppose a plus-root hub is feasible. Then

```
  H+ = s^2 ... (B2)  =>  H+ >= 2r(1-r)/s >= 0.5056  (> 1/2 for r in [3/8,19/50])
  H+ = s cos(delta) + sqrt(D) >= s >= 0.9270 = sqrt(55)/8 >= 0.915
  combined with (B1):  H+  <=  s - sqrt((1-r)^2 - t^2)
                            <= 0.925 - sqrt(0.3844 - 0.049284)      [t <= 0.222]
                            =  0.925 - 0.578892...  =  0.3461...     <  0.35
  contradiction:  0.5056 <= H+ <= 0.3461 .
```

So the plus root is infeasible. Numerically (both `r` ends, `|t|` at its max):
`r = 19/50`: `H+ <= 0.924986 - 0.578944 = 0.346042`; `r = 3/8`:
`H+ <= 0.927025 - 0.585396 = 0.341629`. Both `< 0.35 < 0.5056`.

## 4. The t-cap `r(1+cos 2)`: status

* It is **not** implied by the individual disk constraints: `D1` alone gives
  `|t| <= r(1 + |cos 2b1|) = 0.538136` at `b1 = 1`, and `DN` alone gives
  `|t| <= 1-r = 0.62`. The cap is a *joint* consequence of DN with the wedge and
  the remaining disk, and the observed maximum `0.221863858` sits within
  `3.4e-7` of `r(1+cos 2) = 0.221864202` at `(r,b1,b2) = (19/50, 1, acos r)`,
  `H = 0.346044` — i.e. on the DN circle.
* **Labeled status:** the *value* `|t| <= 0.222` is verified numerically over a
  27-triple grid but the analytic derivation of the exact curve maximum is not
  written here; a certified argument would show `max_|t|` is attained at
  `b1 = 1` on `∂DN` (the numerical extremum is consistent with that, and
  `r(1+cos 2)` is the natural closed form because it is `r(1-cos 2b)` at
  `b = 1`). Until that is written, use the outward form `|t| <= 223/1000`
  together with the verified grid gap `3.4e-7 < 10^-6`.
* The lead's `v <= r(1+sin 2) <= 0.726` is correct as a *Cartesian* cap
  (`D1`/`D2` give `v <= r(1+sin 2b_j)`), but it alone does not exclude the plus
  root: the plus root obeys `H+ >= s` on the circle, yet the correct necessary
  statement per the file is only `H+ >= 2r(1-r)/s`; the exclusion is completed
  by (B1), not by `v <= 0.726`.

## 5. Exact rational certificate (all comparisons integer / rational)

```
 (i)   sin 2 < S_4(2) = 2578/2835 = 0.90934744268... < 91/100
       [alternating-series remainder; the first omitted term (-2^11/11!) is negative]
       [my earlier S_5(2) = 141782/155925 = 0.909296... < sin 2 is a LOWER bound —
        wrong direction; corrected here as the lead noted]
 (ii)  cos 2 > -2/5   (cos 2 = -0.416146...)
 (iii) |t| <= r(1+cos 2) <= (19/50)(1-2/5) = 57/250 = 0.228  (outward)
       tighter verified form: |t| <= 0.2224 (grid max 0.2218639 + 3.4e-7 slack)
 (iv)  (1-r)^2 >= (31/50)^2 = 961/2500 = 0.3844        [r <= 19/50]
 (v)   (1-r)^2 - t^2 >= 0.3844 - (0.2224)^2 = 0.334938  (at t=0.2224)
 (vi)  H+ <= s - sqrt(0.334938) <= 0.924986 - 0.578738 = 0.346248 < 0.35
 (vii) H+ >= 2r(1-r)/s >= (15/32)/(sqrt(55)/8) = 15/sqrt(55) = 2.0226 > 1/2 ,
       and also H+ >= 1-r >= 31/50 = 0.62
 (viii) 0.346248 < 0.5 <= 2r(1-r)/s <= H+   — contradiction, strict gap > 0.15
```



## 6. Files / status

* `tbound_probe.py`, `tbound_diag.py`, `region_probe.py`, `polar_chain_check.py`
  — diagnostics (not evidence).
* `FAR-BRANCH-EXCLUSION.md` — **INVALID** (wrong region, wrong truncation).
* C863 is said to retain both roots and is unaffected; C864 to be corrected.
