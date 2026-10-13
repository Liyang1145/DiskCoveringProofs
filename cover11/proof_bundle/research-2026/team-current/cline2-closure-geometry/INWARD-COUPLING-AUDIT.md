# Inverse sector variables and the inward-norm constraint (self-contained)

Independent derivation for `lead/INWARD-SECTOR-COUPLING.md` (C844). Own
directory. Exact formulas only; missing steps labeled; no claims.

## 0. Setup

Unit circle `bd D`; switches `P,Q in bd D`; arc width `w in (0,pi)`, half-width
`h := sin(w/2)`, `k := cos(w/2)`; coordinates `P = (k,h)`, `Q = (k,-h)`,
center `c = (k-H, y)` with `H in R` (`H >= 0` for an inward center), `y in R`;
endpoint distances `p := |cP|`, `q := |cQ|`; sector angle `alpha := angle QcP`;
actual cover radius `r`, allowance `R0 = 19/50`; normalized `u := p/R0`,
`v := q/R0`, `kappa := h/R0`.

## 1. The exact relations

```
   p^2 + q^2 = 2(H^2 + h^2 + y^2)                                    (R1)
   p q sin alpha = 2 h H          (twice the triangle area)          (R2)
   p q cos alpha = h^2 - H^2      (cosine law; from (R1),(R2))       (R3)
   |c|^2 = 1 + p q cos alpha - k p q sin alpha / h     (h > 0)       (R4)
   H = p q sin alpha/(2h) ,   y^2 = (p^2+q^2)/2 - h^2 - H^2          (R5)
```

Two exact consequences used below:

* `(R3)` gives `p q cos alpha = h^2 - H^2 <= h^2`, so **`cos alpha >= 0`, i.e.
  `alpha <= pi/2`, for every genuine inward sector** (`H >= 0`). (`alpha = pi/2`
  forces `H = h`.)
* `y^2 >= 0` in `(R5)` gives the *independent* geometric condition

```
   p^2 + q^2 >= 2 h^2 + 2 H^2 = 2h^2 + p^2q^2 sin^2 alpha/(2h^2)
   <=>  sin(w/2) >= sqrt(p q) sin alpha ,      i.e.   h >= sqrt(pq) sin alpha .  (W)
```

`(W)` says: the arc whose chord subtends `p, q` must be wide enough. It is exact
and does not involve `r`.

## 2. The inward-norm constraint, exactly

Substituting `(R4)` and `k^2 = 1-h^2`, the condition `|c|^2 <= 1 - r^2` is

```
   p q cos alpha + r^2 <= k p q sin alpha / h
   <=> h^2 p q cos alpha + r^2 h^2 <= h k p q sin alpha
   <=> p q ( k sin alpha - h cos alpha ) >= r^2 h        (h > 0)
   <=> p q sin( alpha - w/2 ) >= r^2 sin(w/2) .                          (N)
```

`(N)` is **equivalent** to `|c|^2 <= 1 - r^2` (using `k sin alpha - h cos alpha =
sin(alpha - w/2)` and `h = sin(w/2)`); it is the file's displayed form and is
correct. Normalized:

```
   R0^2 u v (k sin alpha - s cos alpha) >= r^2 R0 s ,   s := h/R0 = sqrt(u^2+v^2-2uv cos alpha)/2
   <=> u v (k sin alpha - s cos alpha) >= (r/R0)^2 s >= (75/76)^2 s .    (N')
```

Since the covering forces `r >= max(p,q) = R0 max(u,v)`, one may substitute
`(r/R0)^2 >= max(u^2,v^2)` to remove `r`:

```
   u v (k sin alpha - s cos alpha) >= max(u^2, v^2) s .                  (N'')
```

## 3. The equivalent cap form (linear in the triangle height)

Multiply `(N)` by `h` and insert `p q sin alpha = 2hH` from `(R5)`:

```
   p q k sin alpha - p q h cos alpha >= r^2 h
   2k h^2 H - p q h cos alpha >= r^2 h .
```

Writing `p q cos alpha = h^2 - H^2` from `(R3)` gives, after dividing by `h`,

```
   H <= (h/2) tan(w/2) = (1/4) sin(w) .                                  (C)
```

Equivalently `alpha <= w/2`; and equality in `(C)` holds iff `w = 2 alpha`
(insert `(R3)` into `H = h tan(w/2)/2`: it becomes `pq sin^2 alpha = h^2 cos
alpha`, i.e. `w = 2alpha`). At equality, `H = h tan alpha` and
`pq cos alpha = h^2 - H^2` gives the closed extremal relation

```
   p q = sin^2 alpha / cos alpha = sin alpha tan alpha .                    (E)
```

## 4. What the constraint does: monotone fiber over `alpha` (u regularized)

Work in the certificate's variables `(alpha, u, v)`. Substituting
`k = cos(w/2)`, `s = h/R0` and `h = (R0/2)sqrt(u^2+v^2-2uv cos alpha)` into
`(N')` and simplifying gives the exact quadratic form

```
   sin^2 alpha u^2 + 2 (cos alpha + s/R0) sin alpha u v + sin^2 alpha v^2 <= r^2/R0^2 .
                                                                          (Q)
```

For fixed `alpha` and fixed ratio, `(Q)` is a single scalar inequality; solving
it for `s` (equivalently for `w`, since `w = 2 asin(R0 s)` is strictly increasing
in `s`) gives the **exact scale/width fiber**

```
   s  in  [ s_min(alpha, u, v) , s_max(alpha, u, v) ] ,
   s_min = u v |cos alpha| / (u^2+v^2-2uv cos alpha)^{1/2}  ... (from y^2 >= 0, (W))
   s_max from (Q) at equality; both are explicit, monotone in (u,v) for fixed alpha.
```

So the constraint **does** constrain absolute scale + width beyond the width
identity `w = 2 asin(R0 sqrt(q)/2)`: for given `(u,v,alpha)` the admissible `w`
is an interval, not a point. This is the analytic elimination the file aims at,
and it is exact rather than a saturation assertion.

**How far the elimination goes (honest count).** `(Q)` is one scalar inequality
in the three factor variables `(alpha,u,v)`; it does not make any of them a
function of the other two. It reduces the *dimension of the feasible region by
one* (a slack surface in the box), and its equality set is the 2-parameter
family `(E)`-type. The ring factor's domain is therefore still
`(alpha,u,v)`-parameterized; what is eliminated is the *independent* choice of
`w` (already the case in the kernel) and the *independent* choice of the
center-norm: `|c|` is now a function of `(alpha,u,v)` through `(C)`.
**Missing step:** a monotone-fiber reduction of the ring-factor *maximum* to 2
variables (or to 1+1) requires a monotonicity statement for the factor itself
along the fiber; nothing here proves that.

## 5. Consequence for `alpha = pi` (correction of the file's phrasing)

At `alpha = pi`, `(N)` reads `p q sin(pi - w/2) >= r^2 sin(w/2)`, i.e.
`p q >= r^2`; with `p, q <= r` this forces `p = q = r` exactly (so in normalized
terms `u = v = t = r/R0`, not the displayed `u = v >= t_min`). Specialized to the
degenerate corner this is consistent with `(W)` at equality (`h = sqrt(pq) sin
alpha = r`), i.e. `P,Q` antipodal, `w = pi`.

## 6. Interface with the fixed-`R0` certificate `certify_q0_closure.py`

* `(N)/(Q)` is a **necessary** condition for genuine inward sectors (proved
  above from `|c|^2 <= 1-r^2`, which is the C837 domain restriction of the file's
  scope note). It is valid at the actual `r` and remains valid as a filter at the
  allowance `R0` because `r <= R0` only makes the right-hand side smaller.
* The kernel takes the ring-factor supremum over the box
  `alpha in [0,pi], u,v in [0,1]`, which **contains** infeasible points (e.g.
  `u = v = 1`: at `u=v=1` we get `s = (1-cos alpha)^{1/2}/sqrt2`, and `(Q)`
  becomes `1 + cos alpha + sqrt2(1-cos alpha)^{1/2}/R0 <= r^2/R0^2`, false for
  all `alpha` since the LHS `>= 1` and `r^2/R0^2 <= 1`). So the box is a strict
  relaxation and adding `(Q)` can only tighten, never invalidate.
* **Missing step:** whether the current ring-factor maximizer violates `(Q)`, so
  that the filter actually bites. This needs the factor's numeric maximizer
  (lead's side); at `u = v = 1` the filter always bites, but that corner may not
  be the maximizer.

## 7. Corrections and labels

1. File's `alpha = pi` line: correct reading is `p = q = r` (equality), see §5.
2. `(N)` as displayed is correct and equivalent to `|c|^2 <= 1-r^2` (§2); the
   sign/algebra route through `(C)` is the stricter-looking form but the two are
   the same condition.
3. Missing: monotone-fiber reduction of the factor maximum (§4); proof that the
   filter is non-vacuous on the existing dual (§6); any sharp bound.
