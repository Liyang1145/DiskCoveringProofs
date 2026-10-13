# Geometric-mean / log-ratio coordinates: closed scale interval and monotonicity

Own-directory derivation for the lead's parametrization. Exact formulas;
verified identities marked; **missing steps labeled**.

Caliber: `u = p/R0`, `v = q/R0` endpoint distances in units of the allowance
`R0 = 19/50`; `p,q` the raw endpoint distances; `r` the actual cover radius,
`rho := r/R0 in [75/76, 1]`; `w` the sector arc width; `h = sin(w/2)`,
`k = cos(w/2)`; `alpha in (0,pi)` the sector angle at the center.

## 1. Coordinates and exact identities

```
  u = s e^{d} ,  v = s e^{-d} ,  s = sqrt(uv) > 0 ,  d in R ,
  uv = s^2 ,  max(u,v) = s e^{|d|} ,  p q = R0^2 s^2 ,  sqrt(pq) = R0 s .

  Q  := u^2+v^2-2uv cos alpha = 2 s^2 ( cosh 2d - cos alpha )      (V1) [verified]
  h  = (R0/2) sqrt(Q) = R0 s sqrt(2(cosh 2d - cos alpha))/2         (V2) [verified]
  w  = 2 asin( s sqrt(2(cosh 2d - cos alpha))/2 )                   (V3) [verified]
```

`(V1)` makes `alpha`, `d` and `s` independent coordinates for the sector
(`s` = geometric mean of the two endpoint distances).

## 2. The two constraints

**Covering bound** (`max(u,v) <= 1`, since both endpoint distances are `<= r <= R0`):

```
  s e^{|d|} <= 1   <=>   s <= e^{-|d|} =: s_max(d) .                          (S)
```

**Radius / inward-norm condition** (`s^2 sin(alpha - w/2) >= rho^2 sin(w/2)`):

```
  sin(alpha - w/2) >= rho^2 sin(w/2) .                                        (L)
```

**C844 (max-factor condition)** `uv(k sin alpha - s cos alpha) >= max(u^2,v^2) s`
becomes, after dividing by `s^2` and inserting `(V2)`:

```
  sin( alpha - w/2 ) >= e^{2|d|} sin( w/2 ) ,                                 (C844')
  equivalently   tan( w/2 ) <= sin alpha / ( e^{2|d|} + cos alpha ) .         (C844'')
```

Both `(C844')` and `(L)` are of the form `sin(alpha-w/2) >= mu sin(w/2)` with
`mu = e^{2|d|} >= 1` and `mu = rho^2 <= 1`.

## 3. Root, monotonicity, closed forms (proved)

Fix `alpha in (0,pi/2]` and `mu >= 1`; let `Psi(w) := sin(alpha-w/2) - mu sin(w/2)`
on `(0, 2alpha]` (for `w > 2alpha` the inequality fails identically, and
`2alpha <= pi`). Then

```
  Psi'(w) = -(1/2)[ cos(alpha - w/2) + mu cos(w/2) ] < 0    on (0, 2alpha) ,
```

both cosines being positive there. So `Psi` is strictly decreasing,
`Psi(0) = sin alpha > 0`, and `(C844')` is equivalent to `w <= w_max(alpha,mu)`,
the unique root. Closed form (verified to 30 digits):

```
  tan(w_max/2) = sin alpha / ( mu + cos alpha )                               (W)
  w_max = alpha - 2 atan( (mu-1) tan(alpha/2)/(mu+1) )
  sin(w_max/2) = sin alpha / sqrt( mu^2 + 2 mu cos alpha + 1 )
  sin(alpha - w_max/2) = mu sin(w_max/2)         (by the defining equation)
```

`(W)` with `mu = e^{2|d|}` is the lead's bound; at `d = 0` it gives `w_max = alpha`.

## 4. Main structural result: the constraint factors and the scale interval is alpha-independent (proved)

Insert `(V1)` and `(V3)` into `(C844')`: with `w = 2 asin(s sqrt(Q)/2)` and
`tan(w/2) = s sqrt(Q) / (2 sqrt(1 - R0^2 s^2 Q/4))` (from `(V2),(V3)`),
`(C844'')` becomes an equation in `s` alone. Working it out with
`Q = 2s^2(cosh 2d - cos alpha)`:

```
   (C844')  <=>  sin alpha >= e^{2|d|} sin(w/2) + cos alpha cos(w/2)
            <=>  ( after squaring, using 1 - cos^2 = sin^2 )
   [ 1 - e^{4|d|} + R0^2 e^{4|d|} (cosh 2d - cos alpha) ] * s^2 <= 0 .
```

Using `cosh 2d = 1 + 2 sinh^2 d`, the bracket is
`2e^{2|d|}[ (e^{-2|d|}-e^{2|d|})/2 + R0^2 e^{2|d|}(cosh 2d - cos alpha) ]` — in
any case the bracket is strictly negative, so the inequality is

```
   (C844')  <=>  s <= e^{-|d|}  =  s_max(d)          (verified: numerical
   solutions of (C844') at (alpha,d) = (pi/2,0.3),(1.2,0.3) reproduce e^{-|d|} exactly)
```

i.e. **the max-factor condition is *equivalent* to the endpoint-diameter
(covering) bound** in these coordinates: it forces `s max(u,v)^{-1} <= 1`, and
nothing more. That is the factorisation sought. Consequently `(C844')` cannot
produce an upper bound on `s` below `s_max` — relevant to the certificate
reading `3.14516 > pi`.

The real interval comes from `(L)` (the inward-norm condition). At the boundary
`w = w_max` of `(C844')` one has `sin(alpha-w/2) = e^{2|d|} sin(w/2)`, and
substituting `sin(w/2) = R0 s sqrt(2(cosh 2d - cos alpha))/2` into
`s = R0 sin(w/2)/(2 rho sin(alpha-w/2))` gives

```
   s_min(d,rho) = R0 e^{2|d|} / (2 rho)          (alpha-independent!)
```

**Verified:** the middle expression `R0 sin(w/2)/(2 rho sin(alpha-w/2))` at
`w = w_max` gives the same value for `alpha = 0.8, 1.2, 1.5, pi/2` at fixed
`(d,rho)` (30 digits), and the derivation above is a one-line substitution.
Hence

```
   admissible s at fixed (d,rho):   [ s_min , s_max ] = [ R0 e^{2|d|}/(2 rho) ,  e^{-|d|} ]   (I)
```

**Nonemptiness (exact):**

```
  (I) nonempty   <=>   e^{3|d|} <= 2 rho / R0
                 <=>   |d| <= (1/3) ln( 2 rho / R0 ) .
```

At `R0 = 19/50`: `|d| <= 0.55357...` for `rho = 1`, `|d| <= 0.54845...` for
`rho = 75/76`. Beyond that the sector is impossible. Equivalently, the segment
forces the two endpoint distances to be equal to within a factor
`e^{2|d|} <= (2rho/R0)^{2/3} <= (2/R0)^{2/3} = 1.405`:

```
  max(u,v)/min(u,v) <= (2 rho/R0)^{2/3} <= 1.405 .
```

## 5. Interface notes and missing steps

* Since `s_min` is independent of `alpha`, for each `d` the `s`-interval is the
  same for every `alpha`; the `alpha`-dependence now lives only in
  `h = R0 s sqrt(2(cosh 2d - cos alpha))/2` and `w = 2 asin(h/R0)`. The
  3D filter boundary in `(u,v)` is therefore replaced by the two scalar
  inequalities `s >= R0 e^{2|d|}/(2rho)` and `s <= e^{-|d|}`.
* The certificate kernel's box `alpha in [0,pi], u,v in [0,1]` is the relaxation
  dropping `s >= s_min`; adding that scalar cut can only improve a bound, and
  because it is `alpha`-free it does not require new box subdivisions.
* **Missing step 1:** whether the existing dual's maximizer violates
  `s >= s_min` — a one-number question for the numeric exchange. Note the
  `d = 0` diagonal (`u = v`, the envelope's home) has `s >= R0/(2rho) = 0.19`,
  so the cut is far from vacuous there only if the maximizer sits at small `s`.
* **Missing step 2:** the maximization over `alpha` at fixed `(d,s)` of the
  factor's `alpha`-dependent terms was not attempted.
* **Missing step 3:** nothing here proves a sharp value; `R0` remains the
  allowance and `rho <= 1` only enters through `(L)`.

## 6. Corrections of my own earlier wrong forms (for the record)

* `sin(w_max/2) = sin(alpha/2)/sqrt(mu)` is **wrong**; the correct closed form is
  `sin(w_max/2) = sin alpha / sqrt(mu^2 + 2 mu cos alpha + 1)` (verified 30 digits
  against the root; the wrong form fails by up to 0.077 at `mu = 2.718`, `alpha = 1.5`).
* `s_min = R0 sin(alpha/2)/(2rho sqrt(cosh^2 d - sin^2(alpha/2)))` is **wrong**;
  the correct value is `s_min = R0 e^{2|d|}/(2rho)`, which is exactly
  `alpha`-independent (the wrong form varies with `alpha` and misses by up to 0.35).
* The equality set of `(C844')` is the curve `(W)`; **on that curve
  `(C844')` is equivalent to `s = s_max`**, i.e. the max-factor condition is the
  endpoint-diameter condition there. This is why it cannot by itself produce an
  upper bound on `s` below the covering bound — a relevant structural fact for
  the certificate's `3.14516 > pi` reading.
