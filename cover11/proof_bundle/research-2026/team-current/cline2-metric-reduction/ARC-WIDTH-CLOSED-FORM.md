# Arc width `W(r,b)`: corrected exact closed form, bound, and inversion (Round 13, rev 2)

Own directory. **Every formula of my previous version is re-derived here; the four errors the
lead identified are corrected and marked `[was wrong]`.** No numeric verification is claimed for
the withdrawn formulas.

## 0. Notation and the correct domain

```
r in (0,1),  s = sqrt(1-r^2),  alpha := acos r,  phi := asin r   (alpha + phi = pi/2)
b in [alpha/2, alpha],   x := 2b - alpha  in [0, alpha]        [was wrong: I wrote [0, pi-alpha]]
c1 = (s - 2r sin b cos b, -2r sin^2 b),   P1 = (s,-r)
X = cross(c1,P1),  D = c1.P1,  W = 2 atan2(X,D)
```

`b = alpha/2` gives `x = 0` (site at the midpoint, width `0`), `b = alpha` gives `x = alpha`
(the inwardness end). At `r = 0.38`: `alpha = 67.6663`, so `x in [0, 67.6663]`; the value
`x = pi/2 = 90` used in my previous report is **outside** the domain. `[was wrong]`

## 1. The identity and the closed form (correct — the useful part)

Writing `b = (alpha + x)/2` in the coordinates of `c1` gives

```
    X = r sin x ,        D = 1 - r cos x                                   (1)
    W(r,b) = 2 atan2( r sin x , 1 - r cos x ) ,    x = 2b - alpha .        (2)
```

So the lead's guessed shape is right, with `acos r` inside the sine/cosine:

```
    W = 2 atan2( r sin(2b - acos r) , 1 - r cos(2b - acos r) ) .           (3)
```

The literal `2b` form is not correct — the `alpha` shift is essential. Half-angle form:
`tan u = r sin x / (1 - r cos x)` with `u := W/2`.

## 2. Monotonicity and the bound (corrected)

Differentiating (2) (equivalently the half-angle form) gives

```
    dW/db = 2 r (cos x - r) / (1 - 2 r cos x + r^2) .                      (4)
```

`[was wrong]` **This is `>= 0` only for `x <= alpha`** — which is exactly the domain, since
`cos alpha = r`. My previous report used the interval `[0, pi-alpha]`, on which the derivative
changes sign and the monotonicity/bound argument collapses. With `x in [0, alpha]`:

```
    W(0) = 0 ,        W(alpha) = 2 phi = 2 asin r
    =>   0 <= W(r,b) <= 2 asin r ,   equality exactly at x = alpha (b = alpha) .   (5)
```

So `W <= 2 asin r` holds, with the maximum at the inwardness end.
`[was wrong]` The interior candidate `b = alpha/2 + pi/4` (`x = pi/2`) is **not in the domain**;
drop it. Also `2 atan r` and `2r/(1+sqrt(1+r^2))` are different objects: the latter equals
`2 tan(alpha/2)` (the half-angle tangent), not `2 atan r`. `[was wrong]`

## 3. Exact inversion (corrected, now in the simplest form)

`W = g` means `tan(g/2) = r sin x/(1 - r cos x)`. Multiplying by `cos(g/2)` and collecting,

```
    r[ sin x cos(g/2) + cos x sin(g/2) ] = sin(g/2)
    <=>   sin( x + g/2 ) = sin(g/2) / r .                                  (6)
```

Hence the exact inverse:

```
    x_min(g) = asin( sin(g/2) / r ) - g/2 ,      b_min(r,g) = (alpha + x_min(g))/2 .   (7)
```

Real iff `sin(g/2) <= r` (automatic here: `g0/2 = 1.3305 deg`, `r >= 0.375`); increasing in
`g`; `x_min(0) = 0`; and `x_min = alpha` exactly when the sector becomes flat.

`[was wrong]` My previous quadratic claimed discriminant `4(r^2 - t^2)`. The correct
discriminant of the same reduction (`t = tan(g/2)`, `z = tan(x/2)`) is

```
    t(1+r) z^2 - 2 r z + t(1-r) = 0 ,     disc = 4[ r^2 - (1-r^2) t^2 ] .  (8)
```

**Small-`g`.** From (6), `x + g/2 = asin((g/2)/r + O(g^3)) = (g/2)/r + O(g^3)`, hence

```
    x_min(g) = (1/r - 1) g/2 + O(g^3) ,     b_min(r,g) = alpha/2 + (1/r - 1) g/4 + O(g^3) .  (9)
```

`[was wrong]` My previous `x ~ t/r = g/(2r)` dropped the `-g/2`. At `r = 0.38` the leading
term is `x_min ~ 0.8158 g`; at `g0 = 2pi - 16 asin(0.38) = 2.6610775 deg` it gives `2.1708 deg`
(the exact value is slightly larger, the `O(g^3)` term being negative).

## 4. Consequences for the interval contraction

* The floor `W >= g` is exactly the cut `b >= (alpha + asin(sin(g/2)/r) - g/2)/2`, so the
  admissible fibre is `x in [x_min(g), alpha]`, i.e. `b in [b_min(r,g), alpha]`.
* `b_min` is explicit and increasing in `g`, so endpoint bounds for interval arithmetic follow
  from (7)/(9) directly.
* Degenerate ends: `g -> 0` gives `x_min -> 0` (`b_min -> alpha/2`, empty interior); the flat
  sector corresponds to `x_min -> alpha`.

## 5. Status

(1)–(3): the useful exact identities (two lines each). (4)–(5): corrected monotonicity and bound.
(6)–(7): the corrected exact inversion. (8)–(9): corrected discriminant and small-`g`. No numeric
verification is claimed for the withdrawn formulas, and no claim is registered.
