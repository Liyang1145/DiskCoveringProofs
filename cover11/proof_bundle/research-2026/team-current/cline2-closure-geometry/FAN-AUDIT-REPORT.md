# Audit: `lead/FAN-DEFICIT-COORDINATES.md` — fan deficit coordinates and the exact loss identity

Author: cline2-closure-geometry. Scope: this directory only.
**All statements below are proved analytically**; `fan_audit.py` reproduces the
algebra symbolically with sympy, and its numeric printouts are diagnostic only.
Caliber: unit-disk target; equal disks of radius `r <= R`; a hub `H` and two
*consecutive* neighbouring centres `U, V` of the refined structure, with
`|HU| = 2R cos s`, `|HV| = 2R cos t`, `s,t in [0, pi/2]`, hub angle
`theta in (0, pi)`, `R_circ` the circumradius of `HUV`.

## 0. Verdict

| claim in the file | status |
|---|---|
| `cos^2 s + cos^2 t - 2 cos s cos t cos th <= 1`  <=>  `R_circ <= R` (with `a <= 2R`) | **correct** (§1) |
| completing the square is **exactly** `\|s-t\| <= th <= s+t` | **correct, sharp, closed boundary included** (§1) |
| fan area `2R^2 cos s cos t sin th`; ring edge `2R sqrt(cos^2 s + cos^2 t - 2 cos s cos t cos th)` | **correct** (§1) |
| fan radius inequality is linear in deficit angles and hub increments | **correct**, with the right variables: `\|d_i\| <= th_i <= a_i`, `d_i = s_i - s_(i+1)`, `a_i = s_i + s_(i+1)` (§3) |
| complete-star face conditions; consequence `sum s_i >= pi` | **correct** (§4); necessary only |
| zero-spoke limit / `a = 0` ambiguity | **correct**, described precisely (§2) |
| loss identity `R^2 sin th[(1-cos(s-t)) + (cos th - cos(s+t))]` | **correct** (§5) |
| "can this yield a strict shared-edge penalty across degree 6/7 hub stars?" | **NO uniform penalty** — the loss vanishes at the balanced star of every degree; §6 gives the exact criterion and the sharp conditional form |

## 1. The radius equivalence (proof)

`a := |UV|`. The side condition `a <= 2R` is
`cos^2 s + cos^2 t - 2 cos s cos t cos th <= 1`, equivalently

```
  (cos th - cos s cos t)^2 <= sin^2 s sin^2 t .                        (E)
```

Indeed the left side minus the right side factors as

```
  (cos th - cos s cos t)^2 - sin^2 s sin^2 t
      = (cos th - cos(s - t)) (cos th - cos(s + t)) .                   (F)
```

The circumradius is `R_circ = |HU||HV| a/(4K)` with `K = area`; since
`|HU||HV| sin th = 2K` and (by the sine rule) `a = 2R sin th`,

```
  R_circ = (2R cos s)(2R cos t)/(2 sin th) = 2R cos s cos t / sin th ,
```

so `R_circ <= R` is `sin^2 th >= 4 cos^2 s cos^2 t`, which is the same as (E):

```
  sin^2 th - 4cos^2 s cos^2 t = 1 - cos^2 th - (2 cos s cos t)^2
     = ... = -(cos th - cos s cos t)^2 + sin^2 s sin^2 t .
```

Since `s,t in [0,pi/2]` give `s+t in [0,pi]` and `|s-t| in [0,pi/2]`, and `cos`
is decreasing on `[0,pi]`, (F) is equivalent to

```
  cos th <= cos(s - t)  <=>  th >= |s - t| ,      cos th <= cos(s + t)  <=>  th <= s + t .
```

Hence **`R_circ <= R` iff `|s-t| <= th <= s+t`**, for non-degenerate `s,t < pi/2`,
and the equivalence is sharp: `th = |s-t|` (collinear with `U` or `V` between) and
`th = s+t` (`H` on the segment `UV`) are both attained. The feasible region is the
convex cone `{t >= th - s, t <= th + s, t >= 0, s <= pi/2}` in the `(s,t)` plane.

## 2. Extension / degeneracies (exact)

* `s -> 0` or `t -> 0`: the neighbour lies on the circle of radius `2R` about `H`;
  the condition forces `th = t` or `th = s` — a measure-zero boundary. Area
  `-> R^2 sin 2t` (resp. `R^2 sin 2s`), no singularity.
* `s -> pi/2` (spoke collapses): `a -> 2R cos t`, area `-> 0`, `R_circ -> 0`, and
  the condition degenerates to `th <= pi/2 + t` (the lower bound
  `th >= pi/2 - t` persists). Continuous closure, nothing lost.
* `s = t = pi/2`: `U = V = H`; the hub angle is **not defined** — this corner must
  be excluded or handled as a separate combinatorial case (this is exactly what
  the file warns about, and it matters for interval DP: a box around this corner
  contains non-configurations).
* `s = t = 0`: both neighbours on the hub circle; `|s-t| = s+t = 0` forces
  `th = 0`, i.e. the two neighbours coincide (same degeneracy).

## 3. Where the linearity lives

With `d_i := s_i - s_(i+1)` and `a_i := s_i + s_(i+1)` (half the *arc* of the
hub circle owned by neighbour `i`; the neighbours' disks cut arcs `2s_i` on the
hub circle), the face condition is

```
  |d_i| <= th_i <= a_i ,   th_i > 0 ,   sum_i th_i = 2 pi .
```

This is a **difference-constraint chain** in `s_0..s_(d-1}` plus one additive
budget — exactly the file's "1-D chain with one additive angular resource". The
objective `area_i = 2R^2 cos s_i cos s_(i+1) sin th_i` is not linear, so a DP
must carry it (or a certified concave envelope), but the *constraints* are linear.

## 4. Capacity bound (correct, necessary, not sufficient)

Summing `th_i <= a_i` over the `d` faces and using `sum th_i = 2 pi`:

```
  2 pi <= sum_i (s_i + s_(i+1)) = 2 sum_i s_i   =>   sum_i s_i >= pi ,
  equivalently   sum_i acos(rho_i / (2R)) >= pi ,  rho_i = |H c_i| .
```

* `d = 6`: the sum of upper bounds is `2 sum s_i`; equality of budget and bound
  forces `sum s_i = pi` and every `th_i = a_i`. If `sum s_i > pi` there is slack.
* `d = 7`: `sum s_i >= pi` still necessary; the per-edge budget `th_i <= 2s_i` is
  looser than the total budget, so slack is typical.
* The converse is false: `sum s_i >= pi` does not imply the per-face difference
  constraints; do not replace them by the sum.

## 5. Area, envelope, exact loss identity

Per face, `K_i = 2R^2 cos s_i cos s_(i+1) sin th_i`. Using
`2 cos s cos t = cos(s+t) + cos(s-t)` and the constraint `s+t >= th`:

```
  2 cos s cos t <= 1 + cos th          (2cos s cos t = cos(s+t)+cos(s-t) <= 1 + cos th)
```

with equality iff `s+t = th` **and** `s-t = 0`, i.e. `s = t = th/2`. Hence at
fixed `th`

```
  K_i <= R^2 sin th_i (1 + cos th_i) = 2 R^2 sin(th_i) cos^2(th_i/2) ,        (ENV)
```

and subtracting gives the **exact loss identity**

```
  R^2 sin th(1 + cos th) - K = R^2 sin th [ (1 - cos(s-t)) + (cos th - cos(s+t)) ] .   (L)
```

Both brackets are `>= 0` on the feasible set. Equivalently, using
`1 - cos(s-t) = 2 sin^2((s-t)/2)` and
`cos th - cos(s+t) = 2 sin((s+t+th)/2) sin((s+t-th)/2)`:

```
  loss / R^2 = 2 sin th [ sin^2((s-t)/2) + sin((a+th)/2) sin((a-th)/2) ] ,  a = s+t .  (L')
```

**When is the loss zero?** (L) shows `loss = 0` iff `cos(s-t) = 1` and
`cos(s+t) = cos th`, i.e. `s = t` and `s+t = th` (resp. `s+t = 2pi - th`, which
is outside `s+t <= pi` unless `th = pi` and `s+t = pi`, a degenerate case with
`H` on `UV`). So

```
  loss_i = 0   <=>   s_i = s_(i+1) = th_i/2 .
```

## 6. Strict shared-edge penalty for degree 6/7 stars: the exact answer

Let `Lambda := sum_(i=0)^(d-1) [R^2 sin th_i(1+cos th_i) - K_i]` and
`T := sum_i s_i`.

**Proposition 1 (zero-loss characterization).** `Lambda = 0` iff every face is
balanced, `s_i = s_(i+1) = th_i/2` for all `i`. Summing `th_i = 2s_i` over the
cycle gives `2 pi = 2T`, hence

```
  Lambda = 0  <=>  s_0 = ... = s_(d-1) = pi/d  and  th_0 = ... = th_(d-1) = 2pi/d ,
```

for **every** degree `d` — including `d = 6` and `d = 7`.

**Proposition 2 (conditional sharp form).** For every star,
`Lambda >= R^2 sum_i sin th_i (1 - cos(s_i - s_(i+1))) >= R^2 sum_i sin th_i (s_i - s_(i+1))^2 / 2`,
with equality in the first inequality iff every `th_i = a_i` (full saturation).
In particular, if some `th_i < a_i` then `Lambda > 0` strictly.

**Proposition 3 (no uniform gap for `d = 6` or `d = 7`).** By Prop. 1 the
infimum of `Lambda` over locally feasible stars is `0`, attained at the balanced
star `s_i = pi/d`, `th_i = 2pi/d`, which satisfies all the local face conditions
(`|d_i| = 0 <= th_i`, `th_i = 2pi/d = a_i`, `sum th_i = 2pi`) and the capacity
bound with equality (`sum s_i = pi`).

Therefore **the loss identity alone does NOT yield a strict shared-edge penalty
for degree 6 or degree 7 hub stars**; there is no positive constant `c(R^2)`
bounding `Lambda` from below.

**Why the question nonetheless has content.** The balanced stars are locally
feasible but *not* renderable in a cover at radius `R`: with every neighbour at
`rho = 2R cos(pi/d)` from the hub, the perpendicular bisector between two
consecutive neighbours is at distance `2R cos(pi/d) cos(pi/d)` from the hub
(both spokes at angle `pi/d` to the bisector), while the cover requires every
point to be within `R` of a centre. Concretely

```
  d = 6: rho = 2R cos(pi/6) = 1.7321 R ,  bisector distance = 1.5 R > R ;
  d = 7: rho = 2R cos(pi/7) = 1.8019 R ,  bisector distance = 1.8020 R > R .
```

So a genuine cover must deviate from the balance at every star, and any such
deviation produces a strictly positive loss by Props. 1–2 — but the size of the
loss is governed by *how much* the star deviates, which is a global (ring/cover)
condition, not something the local deficit data can supply. In particular the
"shared-edge penalty" cannot be banked as a uniform `R^2`-positive term in a
local fan certificate.

## 7. Honest scope for the certificate route

1. The exact identity (L') is a genuine equality and can be used *inside* an
   interval DP: `area = envelope - imbalance - angle-gap`, both gaps nonnegative.
2. The capacity bound `sum s_i >= pi` is a real linear cut in the deficit chain.
3. The loss is **not** uniformly positive, so it cannot by itself produce the
   strict penalty the file hopes for; a positive penalty requires a global input
   (the cover condition excluding balanced stars), which is exactly the kind of
   "standalone star capacity is insufficient" statement the file already makes.
4. Consequence for the interval-DP proposal: bins must be in
   `(s, accumulated theta)` — correct — but the objective must retain the
   nonlinear `2 cos s cos t sin th`, and the DP cannot assume a positive floor
   on the loss.

## 8. Evidence

* `fan_audit.py` — sympy verification of (F), (ENV), (L) and the closed constants;
  diagnostic numerics for the claimed radii (`1.7321R`, `1.8019R`) and the
  bisector distances (`1.5R`, `1.8020R`).
* This report.
